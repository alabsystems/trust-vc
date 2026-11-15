// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real native component controls. The foreign diagnostic fixture supplies no
//! genuine build/import/ownership permission and cannot call the live API.

extern crate rustc_driver;

use super::*;
use crate::reader::{read_crate, CrateRead, ReadOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
struct Emit;
impl Callbacks for Emit {}
type Inspect = for<'tcx> fn(TyCtxt<'tcx>, &CrateRead);
struct Capture {
    inspect: Inspect,
    ran: bool,
}
impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        let read = read_crate(tcx, ReadOptions::default());
        (self.inspect)(tcx, &read);
        self.ran = true;
        Compilation::Stop
    }
}
fn arguments(source: &Path, output: &Path, name: &str) -> Vec<String> {
    vec![
        "native-ghost-value-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        format!("--crate-name={name}"),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        output.to_str().unwrap().into(),
        source.to_str().unwrap().into(),
    ]
}
fn native(source: &str, inspect: Inspect, diagnostic: bool) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-ghost-value-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("foreign.rs");
    std::fs::write(
        &foreign,
        r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::assert_"]
pub fn assert_(_value: bool) {}
pub fn unknown(_value: bool) -> bool { true }
"#,
    )
    .unwrap();
    rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&foreign, &directory.0, "ghost_value_builtin_fixture"),
            &mut Emit,
        )
    })
    .expect("the actual foreign component fixture must compile");
    let client = directory.0.join("client.rs");
    std::fs::write(
        &client,
        format!(
            r#"#![feature(register_tool, rustc_attrs)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case, internal_features)]
{source}
"#
        ),
    )
    .unwrap();
    let mut args = arguments(&client, &directory.0, "ghost_value_client");
    args.extend([
        "--extern".into(),
        format!(
            "ghost_value_builtin_fixture={}",
            directory
                .0
                .join("libghost_value_builtin_fixture.rmeta")
                .display()
        ),
    ]);
    let mut callback = Capture {
        inspect,
        ran: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback));
    assert!(
        callback.ran,
        "the actual native analysis callback must be reached"
    );
    assert_eq!(
        result.is_err(),
        diagnostic,
        "only the explicit later diagnostic may reject compilation"
    );
}
fn named(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id)
        .find(|definition| {
            tcx.opt_item_name(definition.to_def_id())
                .is_some_and(|actual| actual.as_str() == name)
        })
        .unwrap()
}
fn positive(tcx: TyCtxt<'_>, read: &CrateRead) {
    assert!(read.errors.is_empty(), "{:?}", read.errors);
    assert!(read.refusals().next().is_none());
    assert!(read.verify_refusals.is_empty());
    assert!(read.native_ownership.is_empty());
    for name in ["Good", "Repeated", "Pure", "UsesPure"] {
        let definition = named(tcx, name);
        let ghost = read
            .ghost_ownership
            .get(&definition)
            .expect("a genuine original ghost-value component must be captured");
        assert!(ghost.current(tcx, definition));
        assert!(!ghost.current(
            tcx,
            named(tcx, if name == "Good" { "Pure" } else { "Good" })
        ));
    }
    let owner = named(tcx, "Good");
    let body = tcx.hir_body_owned_by(owner);
    let copied = *body;
    assert_eq!(body.id(), copied.id());
    assert!(original_body(tcx, owner, body));
    assert!(
        !original_body(tcx, owner, &copied),
        "equal original IDs cannot replace the original native body"
    );
    let ghost = &read.ghost_ownership[&owner];
    assert!(!ghost.builtins().is_empty());
    assert!(ghost
        .builtins()
        .iter()
        .all(|definition| !definition.is_local()));
    let mut exhausted = Work {
        remaining: 0,
        refused: false,
    };
    assert!(exhausted.charge(tcx, 1).is_none());
    assert!(
        exhausted.charge(tcx, 0).is_none(),
        "work refusal must remain sticky"
    );
}
#[test]
fn original_ghost_value_components_preserve_owner_and_body_identity() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Good(value: bool) { ghost_value_builtin_fixture::assert_(value); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Repeated(value: bool) { ghost_value_builtin_fixture::assert_(value == value); }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
pub fn Pure(value: bool) -> bool { !value }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn UsesPure(value: bool) { ghost_value_builtin_fixture::assert_(Pure(value)); }
"#,
        positive,
        false,
    );
}
fn declined(tcx: TyCtxt<'_>, read: &CrateRead) {
    // This proves that an empty tracked-root set does not make Exec pure code
    // ownership-ready. Other fixtures are explicit unsupported/owned uses.
    let exec = named(tcx, "Exec");
    assert!(!read.native_ownership.contains(&exec));
    for name in [
        "Exec", "Tracked", "Local", "Nested", "Closure", "Foreign", "Deep",
    ] {
        assert!(
            !read.ghost_ownership.contains_key(&named(tcx, name)),
            "{name}"
        );
    }
    assert!(
        read.ghost_ownership.contains_key(&named(tcx, "Control")),
        "the refusal group must retain a genuine positive control"
    );
}
#[test]
fn owned_exec_and_unrepresented_native_values_never_become_zero_obligations() {
    native(
        r#"
#[verus::internal(verus_macro)]
pub fn Exec(value: bool) -> bool { value }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Tracked(#[verus::internal(proof)] _value: bool) { ghost_value_builtin_fixture::assert_(true); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Local(value: bool) { let current = value; ghost_value_builtin_fixture::assert_(current); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Nested(value: bool) { fn inner() {} ghost_value_builtin_fixture::assert_(value); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Closure() { let function = || true; ghost_value_builtin_fixture::assert_(function()); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Foreign(value: bool) { ghost_value_builtin_fixture::assert_(ghost_value_builtin_fixture::unknown(value)); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Control(value: bool) { ghost_value_builtin_fixture::assert_(value); }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
pub fn Deep(value: bool) -> bool { !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!value }
"#,
        declined,
        false,
    );
    // The extern remains genuinely unused here, so its diagnostic item is not
    // loaded alongside this local forged candidate. No duplicate-ID failure
    // may stand in for the classifier's actual local-identity refusal.
    native(
        r#"
#[rustc_diagnostic_item = "verus::verus_builtin::assert_"]
pub fn forged_assert(_value: bool) {}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Target(value: bool) { forged_assert(value); }
"#,
        |tcx, read| {
            assert!(!read.ghost_ownership.contains_key(&named(tcx, "Target")));
        },
        false,
    );
}
fn revoked(tcx: TyCtxt<'_>, read: &CrateRead) {
    let owner = named(tcx, "Target");
    let ghost = read.ghost_ownership.get(&owner).unwrap();
    assert!(ghost.current(tcx, owner));
    let _error = tcx
        .dcx()
        .err("native ghost-value component invalidation control");
    assert!(!ghost.current(tcx, owner));
}
#[test]
fn later_native_diagnostics_revoke_original_ghost_value_components() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(proof)]
pub fn Target(value: bool) { ghost_value_builtin_fixture::assert_(value); }
"#,
        revoked,
        true,
    );
}
