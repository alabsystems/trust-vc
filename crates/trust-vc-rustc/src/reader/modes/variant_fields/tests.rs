// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native mode-rule fixtures only. The counterfeit foreign diagnostic item
//! supplies no fresh-build, macro, import, representation or ownership authority.

extern crate rustc_driver;

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::adjustment::Adjust;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;
use trust_vc_vcir::Mode;

use crate::reader::attrs::ItemAttrs;
use crate::reader::declaration_modes::DeclarationModes;
use crate::verus_items::VerusItem;

use super::super::{check_with_context, ModeCheck, ModeContext, TAG_MODES_UNKNOWN};

const MARKER: &str = "verus::verus_builtin::get_variant_field";
const OTHER_MARKER: &str = "trust_vc::variant_field_fixture::other";
const IDENTITY: &str = "the field intrinsic lacks its current genuine builtin selection";
const REPRESENTATION: &str = "the field intrinsic cannot inspect this datatype's representation";
static NEXT: AtomicU64 = AtomicU64::new(0);

struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

type Inspect = for<'tcx> fn(TyCtxt<'tcx>);
struct Capture {
    inspect: Inspect,
    ran: bool,
}
impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        (self.inspect)(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        self.ran = true;
        Compilation::Stop
    }
}
struct Emit;
impl Callbacks for Emit {}

fn arguments(path: &Path, output: &Path, name: &str) -> Vec<String> {
    vec![
        "native-variant-field-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        format!("--crate-name={name}"),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        output.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ]
}

fn native(source: &str, foreign: bool, inspect: Inspect) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-variant-fields-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let client = directory.0.join("client.rs");
    std::fs::write(
        &client,
        format!(
            r#"#![feature(register_tool, rustc_attrs, never_type)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, internal_features)]
{source}
"#
        ),
    )
    .unwrap();
    let mut argv = arguments(&client, &directory.0, "native_variant_field_client");
    if foreign {
        let fixture = directory.0.join("foreign.rs");
        std::fs::write(
            &fixture,
            r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::get_variant_field"]
pub fn get_variant_field<A, F>(_value: A, _variant: &str, _field: &str) -> F { loop {} }
#[rustc_diagnostic_item = "trust_vc::variant_field_fixture::other"]
pub fn other() {}
pub enum Foreign { Value(bool) }
"#,
        )
        .unwrap();
        let emit = arguments(&fixture, &directory.0, "variant_builtin_fixture");
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&emit, &mut Emit))
            .expect("the actual foreign fixture must compile before the client");
        argv.extend([
            "--extern".into(),
            format!(
                "variant_builtin_fixture={}",
                directory
                    .0
                    .join("libvariant_builtin_fixture.rmeta")
                    .display()
            ),
        ]);
    }
    let mut callback = Capture {
        inspect,
        ran: false,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut callback))
        .expect("every client must reach actual native analysis without diagnostics");
    assert!(callback.ran, "the genuine analysis callback must run");
}

fn named(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id)
        .find(|owner| {
            tcx.opt_item_name(owner.to_def_id())
                .is_some_and(|actual| actual.as_str() == name)
        })
        .expect("the actual native fixture contains the requested declaration")
}

/// This scoped test context exercises the rule, not production source licensing.
/// It retains the genuine declaration index and permits one original LOCAL ADT.
struct Context<'tcx> {
    index: DeclarationModes<'tcx>,
    target: Option<DefId>,
    selected: Option<DefId>,
}
impl<'tcx> Context<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, selected: Option<DefId>, allow: bool) -> Self {
        let target = named(tcx, "Target").to_def_id();
        assert!(target.is_local());
        Self {
            index: DeclarationModes::new(tcx),
            target: allow.then_some(target),
            selected,
        }
    }
}
impl<'tcx> ModeContext<'tcx> for Context<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.index.tcx()
    }
    fn function_mode(&self, def: DefId) -> Option<Mode> {
        self.index.function_mode(def)
    }
    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.index.body_owner(def)
    }
    fn declaration_attrs(&self, def: LocalDefId) -> ItemAttrs {
        self.index.declaration_attrs(def)
    }
    fn verus_item(&self, def: DefId) -> Option<VerusItem> {
        self.index.verus_item(def)
    }
    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.index.constant_proxy(def)
    }
    fn constant_mode(&self, def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.index.constant_mode(def)
    }
    fn friendly_fn_path(&self, def: DefId) -> String {
        self.index.friendly_fn_path(def)
    }
    fn read_adt_field_modes(&self) -> bool {
        false
    }
    fn permits_adt_fields(&self, def: DefId) -> bool {
        assert!(
            def.is_local(),
            "foreign receivers must stop before local field permission"
        );
        self.target == Some(def)
    }
    fn variant_field_intrinsic(&self) -> Option<DefId> {
        self.selected
    }
}

fn selected(tcx: TyCtxt<'_>) -> DefId {
    let definition = tcx.get_diagnostic_item(Symbol::intern(MARKER)).unwrap();
    assert!(!definition.is_local());
    definition
}

fn call<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> &'tcx hir::Expr<'tcx> {
    let mut expression = tcx.hir_maybe_body_owned_by(owner).unwrap().value;
    loop {
        match expression.kind {
            hir::ExprKind::Block(block, None) if block.stmts.is_empty() => {
                expression = block.expr.expect("fixture body has its actual tail call")
            }
            hir::ExprKind::DropTemps(inner) => expression = inner,
            hir::ExprKind::Call(_, _) => return expression,
            _ => panic!("fixture must retain its actual native tail call"),
        }
    }
}

fn unknown(tcx: TyCtxt<'_>, context: &Context<'_>, name: &str, detail: &str) {
    match check_with_context(context, named(tcx, name)) {
        ModeCheck::Unknown(refusal) => {
            assert_eq!(refusal.tag, TAG_MODES_UNKNOWN);
            assert_eq!(refusal.detail, detail, "wrong refusal for {name}");
        }
        result => panic!("{name} must remain Unknown, got {result:?}"),
    }
}

fn error(tcx: TyCtxt<'_>, context: &Context<'_>, name: &str, message: &str) {
    match check_with_context(context, named(tcx, name)) {
        ModeCheck::Error(error) => {
            assert!(matches!(error.phase, crate::messages::Phase::Modes));
            assert_eq!(error.message, message);
            assert_eq!(error.span, call(tcx, named(tcx, name)).span);
        }
        result => panic!("{name} must report its exact mode error, got {result:?}"),
    }
}

#[test]
fn native_variant_field_modes_keep_real_instantiations_and_never_adjustments() {
    native(
        r#"
use variant_builtin_fixture::get_variant_field;
pub enum Target<A> { Value(A) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn boolean(value: Target<bool>) -> bool { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn tuple(value: Target<(!,)>) -> (!,) { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn generic<A>(value: Target<A>) -> A { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn shared(value: &Target<bool>) -> bool { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn borrowed<'a>(value: Target<&'a bool>) -> &'a bool { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn never(value: Target<!>) -> ! { get_variant_field::<_, !>(value, "Value", "0") }
#[verus::internal(verus_macro)]
fn executable(value: Target<bool>) -> bool { get_variant_field(value, "Value", "0") }
"#,
        true,
        |tcx| {
            let marker = selected(tcx);
            let context = Context::new(tcx, Some(marker), true);
            for name in ["boolean", "tuple", "generic", "shared", "borrowed"] {
                let owner = named(tcx, name);
                let expression = call(tcx, owner);
                let hir::ExprKind::Call(callee, _) = expression.kind else {
                    unreachable!()
                };
                let hir::ExprKind::Path(ref path) = callee.kind else {
                    unreachable!()
                };
                let types = tcx.typeck(owner);
                assert!(matches!(types.qpath_res(path, callee.hir_id),
                Res::Def(DefKind::Fn, actual) if actual == marker));
                match name {
                    "tuple" => {
                        assert!(matches!(types.expr_ty(expression).kind(), ty::Tuple(values)
                    if values.len() == 1 && values[0].is_never()))
                    }
                    "generic" => assert!(matches!(types.expr_ty(expression).kind(), ty::Param(_))),
                    "borrowed" => assert!(matches!(types.expr_ty(expression).kind(),
                    ty::Ref(_, inner, mutability) if matches!(inner.kind(), ty::Bool)
                        && !mutability.is_mut())),
                    _ => assert!(matches!(types.expr_ty(expression).kind(), ty::Bool)),
                }
                let ModeCheck::Clean(checked) = check_with_context(&context, owner) else {
                    panic!("{name} must complete the shared native mode walk");
                };
                assert_eq!(checked.signature.def_id, owner.to_def_id());
                assert_eq!(checked.signature.ret.mode, Mode::Spec);
            }
            let owner = named(tcx, "never");
            let expression = call(tcx, owner);
            let types = tcx.typeck(owner);
            assert!(types.expr_ty(expression).is_never());
            assert!(
                types
                    .expr_adjustments(expression)
                    .iter()
                    .any(|a| matches!(a.kind, Adjust::NeverToAny)),
                "the negative needs a REAL native adjustment"
            );
            error(
                tcx,
                &context,
                "never",
                crate::messages::modes::NEVER_TO_ANY_SPEC,
            );
            error(
                tcx,
                &context,
                "executable",
                crate::messages::modes::GET_VARIANT_IN_EXEC,
            );
        },
    );
}

#[test]
fn native_variant_field_modes_refuse_malformed_metadata_and_missing_permissions() {
    native(
        r#"
use variant_builtin_fixture::{get_variant_field, Foreign};
pub enum Target { Value(bool) }
pub enum Other { Value(bool) }
const LABEL: &str = "Value";
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn valid(value: Target) -> bool { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn wrong_variant(value: Target) -> bool { get_variant_field(value, "Absent", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn wrong_field(value: Target) -> bool { get_variant_field(value, "Value", "absent") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn not_literal(value: Target) -> bool { get_variant_field(value, LABEL, "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn not_literal_field(value: Target) -> bool { get_variant_field(value, "Value", LABEL) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn wrong_type(value: Target) -> u8 { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn foreign(value: Foreign) -> bool { get_variant_field(value, "Value", "0") }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn other(value: Other) -> bool { get_variant_field(value, "Value", "0") }
"#,
        true,
        |tcx| {
            let marker = selected(tcx);
            let context = Context::new(tcx, Some(marker), true);
            assert!(
                matches!(
                    check_with_context(&context, named(tcx, "valid")),
                    ModeCheck::Clean(_)
                ),
                "the same actual call must be valid before removing identity or field permission"
            );
            for (name, detail) in [
                (
                    "wrong_variant",
                    "the field intrinsic has no such native variant",
                ),
                (
                    "wrong_field",
                    "the field intrinsic has no such native field",
                ),
                (
                    "not_literal",
                    "the field intrinsic requires actual string literals",
                ),
                (
                    "not_literal_field",
                    "the field intrinsic requires actual string literals",
                ),
                (
                    "wrong_type",
                    "the field intrinsic result differs from the actual instantiated field type",
                ),
                ("foreign", REPRESENTATION),
                ("other", REPRESENTATION),
            ] {
                unknown(tcx, &context, name, detail);
            }
            unknown(tcx, &Context::new(tcx, None, true), "valid", IDENTITY);
            let wrong = tcx
                .get_diagnostic_item(Symbol::intern(OTHER_MARKER))
                .unwrap();
            assert!(!wrong.is_local() && wrong != marker);
            unknown(
                tcx,
                &Context::new(tcx, Some(wrong), true),
                "valid",
                IDENTITY,
            );
            unknown(
                tcx,
                &Context::new(tcx, Some(marker), false),
                "valid",
                REPRESENTATION,
            );
            assert!(
                matches!(
                    DeclarationModes::new(tcx).check(named(tcx, "valid")),
                    ModeCheck::Unknown(_)
                ),
                "the ordinary declaration context stays unlicensed"
            );
        },
    );
}

#[test]
fn local_counterfeit_variant_field_diagnostic_item_never_gets_clean_modes() {
    native(
        r#"
pub enum Target { Value(bool) }
#[rustc_diagnostic_item = "verus::verus_builtin::get_variant_field"]
fn get_variant_field<A, F>(_value: A, _variant: &str, _field: &str) -> F { loop {} }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn forged(value: Target) -> bool { get_variant_field(value, "Value", "0") }
"#,
        false,
        |tcx| {
            let marker = tcx.get_diagnostic_item(Symbol::intern(MARKER)).unwrap();
            assert!(marker.is_local());
            unknown(
                tcx,
                &Context::new(tcx, Some(marker), true),
                "forged",
                IDENTITY,
            );
        },
    );
}
