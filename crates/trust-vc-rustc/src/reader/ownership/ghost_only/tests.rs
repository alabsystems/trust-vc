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

mod availability_uses;
mod field_modes;
mod ghost_tails;
mod new_references;
mod seq_len;
mod unit_effects;
mod unwind;

#[test]
fn native_after_borrow_requires_original_local_root() {
    availability_uses::after_borrow_place_grammar();
}

#[test]
fn native_availability_modes_preserve_real_accesses_and_erasure() {
    availability_uses::accesses_and_argument_erasure();
}

#[test]
fn native_availability_modes_preserve_explicit_prophecy_suppression() {
    availability_uses::explicit_prophecy_suppression();
}

#[test]
fn native_availability_modes_keep_proof_borrow_and_closed_contexts_distinct() {
    availability_uses::proof_borrow_and_rejected_contexts();
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
struct Emit;
impl Callbacks for Emit {}
type Inspect = for<'tcx> fn(TyCtxt<'tcx>, &CrateRead);
struct Capture {
    inspect: Inspect,
    ran: bool,
    options: ReadOptions,
}
impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        let read = read_crate(tcx, self.options);
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
    native_options(source, inspect, diagnostic, ReadOptions::default());
}
fn native_options(source: &str, inspect: Inspect, diagnostic: bool, options: ReadOptions) {
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
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_current"]
pub fn mut_ref_current<T>(_value: &mut T) -> T { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_future"]
pub fn mut_ref_future<T>(_value: &mut T) -> T { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::final_"]
pub fn final_<T: ?Sized>(value: &mut T) -> &mut T { value }
#[rustc_diagnostic_item = "verus::verus_builtin::has_resolved"]
pub fn has_resolved<T>(_value: T) -> bool { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::has_resolved_unsized"]
pub fn has_resolved_unsized<T: ?Sized>(_value: &T) -> bool { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::decreases"]
pub fn decreases<T>(_measure: T) {}
#[rustc_diagnostic_item = "verus::verus_builtin::spec_eq"]
pub fn spec_eq<T>(_left: T, _right: T) -> bool { unimplemented!() }
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
            r#"#![feature(register_tool, rustc_attrs, stmt_expr_attributes)]
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
        options,
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

// These controls inspect actual native HIR transport. The fixture dependency
// above grants no genuine SDK, macro, import, or verification authority.
#[test]
fn prophetic_native_attributes_preserve_declarations_instances_and_generated_results() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Generic<T>(value: T) -> T { value }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Pure() -> bool {
    #[verifier::prophetic] let explicit = true;
    #[verus::internal(spec)] #[verus::internal(infer_proph)] let (first, second) = (true, false);
    Generic::<bool>(explicit && (first || second))
}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Echo(value: bool) -> bool { value }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Locals() {
    #[verifier::prophetic] let explicit = true;
    #[verus::internal(spec)] #[verus::internal(infer_proph)] let mut delayed;
    delayed = false;
    #[verifier::prophetic] let (first, second) = (true, false);
    let ordinary;
    ordinary = false;
    let call_result = Echo(explicit);
    let branch_result = if explicit { Echo(true) } else { Echo(false) };
    let short_result = explicit && Echo(false);
}
"#,
        |tcx, read| {
            use trust_vc_vcir::{DeclProphecy, FnRole, LocalKind, Mode};
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            assert!(read.refusals().next().is_none());
            assert!(
                read.verify_refusals.is_empty(),
                "{:?}",
                read.verify_refusals
            );
            let declaration = |name| {
                let owner = named(tcx, name);
                read.krate
                    .fns
                    .iter()
                    .find(|function| read.fn_defs.get(&function.id) == Some(&owner))
                    .expect("the original named function must be lowered")
            };
            for name in ["Generic", "Pure"] {
                assert!(declaration(name).attrs.prophetic);
            }
            assert!(!declaration("Echo").attrs.prophetic);
            assert!(!declaration("Locals").attrs.prophetic);
            let instances = read
                .krate
                .fns
                .iter()
                .filter(|function| function.role == FnRole::Instance)
                .collect::<Vec<_>>();
            assert_eq!(instances.len(), 1);
            assert!(instances[0].attrs.prophetic);
            assert!(instances[0].attrs.instance.is_some());
            let local = |function: &trust_vc_vcir::FnDecl, name: &str| {
                function
                    .locals
                    .iter()
                    .find(|local| local.name == name)
                    .expect("the actual source binding must survive")
                    .prophecy
            };
            let pure = declaration("Pure");
            assert_eq!(local(pure, "explicit"), DeclProphecy::Prophetic);
            for name in ["first", "second"] {
                assert_eq!(local(pure, name), DeclProphecy::DelayedInfer);
            }
            let locals = declaration("Locals");
            for name in ["explicit", "first", "second"] {
                assert_eq!(local(locals, name), DeclProphecy::Prophetic);
            }
            assert_eq!(local(locals, "delayed"), DeclProphecy::DelayedInfer);
            assert_eq!(local(locals, "ordinary"), DeclProphecy::Default);
            let temps = locals
                .locals
                .iter()
                .filter(|local| local.kind == LocalKind::Temp)
                .collect::<Vec<_>>();
            assert_eq!(
                temps.len(),
                7,
                "four calls, two expression results, one initialized tuple"
            );
            assert!(temps.iter().all(|local| local.mode == Mode::Spec));
            assert_eq!(
                temps
                    .iter()
                    .filter(|local| local.prophecy == DeclProphecy::DelayedInfer)
                    .count(),
                6
            );
            assert_eq!(
                temps
                    .iter()
                    .filter(|local| local.prophecy == DeclProphecy::Default)
                    .count(),
                1
            );
            for function in &read.krate.fns {
                assert!(function
                    .params
                    .iter()
                    .all(|id| function.locals[id.index()].prophecy == DeclProphecy::Default));
                assert_eq!(
                    function.locals[function.ret.index()].prophecy,
                    DeclProphecy::Default
                );
            }
        },
        false,
    );
}

#[test]
fn prophetic_native_annotations_reject_non_spec_function_and_original_local_modes() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(proof)] #[verifier::prophetic]
fn Proof() {}
#[verus::internal(verus_macro)] #[verifier::prophetic]
fn Exec() {}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Local() { #[verus::internal(proof)] #[verifier::prophetic] let tracked = true; }
"#,
        |_tcx, read| {
            let messages = read
                .errors
                .iter()
                .map(|error| error.message.as_str())
                .collect::<Vec<_>>();
            assert_eq!(
                messages
                    .iter()
                    .filter(|message| **message
                        == "prophetic attribute can only be applied to 'spec' functions")
                    .count(),
                2
            );
            assert_eq!(
                messages
                    .iter()
                    .filter(|message| **message == "only a ghost variable can be prophetic")
                    .count(),
                1
            );
        },
        false,
    );
}

#[test]
fn native_unit_values_preserve_raw_effects_and_clear_them_at_upstream_consumers() {
    unit_effects::native_unit_values_preserve_raw_effects_and_clear_them_at_upstream_consumers();
}

#[test]
fn native_new_reference_spec_intrinsics_preserve_opaque_types_and_resolved_definitions() {
    new_references::native_new_reference_spec_intrinsics_preserve_opaque_types_and_resolved_definitions();
}

#[test]
fn native_new_reference_exec_storage_and_first_class_final_remain_explicitly_closed() {
    new_references::native_new_reference_exec_storage_and_first_class_final_remain_explicitly_closed();
}

#[test]
fn native_ghost_block_tail_preserves_raw_proof_mode_effects() {
    ghost_tails::native_ghost_block_tail_preserves_raw_proof_mode_effects();
}

#[test]
fn native_ghost_block_wrappers_branches_and_instances_retain_checked_modes() {
    ghost_tails::native_ghost_block_wrappers_branches_and_instances_retain_checked_modes();
}
