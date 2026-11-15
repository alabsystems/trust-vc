// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native binder correspondence controls, not a genuine macro/helper positive.
//! Explicit tool markers exercise policy parsing, never macro authentication.

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use super::*;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn named(tcx: TyCtxt<'_>, name: &str) -> DefId {
    tcx.hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id.to_def_id())
        .find(|owner| {
            tcx.opt_item_name(*owner)
                .is_some_and(|actual| actual.as_str() == name)
        })
        .unwrap()
}

fn unknown(result: Result<(), Failure>, expected: &str) {
    match result {
        Err(Failure::Unknown(reason)) => assert_eq!(reason, expected),
        _ => panic!("the mismatched native binder must remain Unknown"),
    }
}

fn inline_controls(tcx: TyCtxt<'_>, ordered: DefId, work: &mut Work) {
    use crate::reader::{attrs, declaration_modes::DeclarationModes, modes};
    use trust_vc_vcir::Mode;
    let local = ordered.expect_local();
    let checked =
        inline::capture(tcx, local, work).unwrap_or_else(|_| panic!("canonical inline must parse"));
    let original = tcx.hir_attrs(tcx.local_def_id_to_hir_id(local));
    let permitted = original
        .iter()
        .filter(|attribute| checked.permits(tcx, local, attribute))
        .collect::<Vec<_>>();
    assert_eq!(permitted.len(), 1);
    let copied: rustc_attr_ir::Attribute = (*permitted[0]).clone();
    assert!(!checked.permits(tcx, local, &copied));
    assert!(!checked.permits(tcx, named(tcx, "own_generic").expect_local(), permitted[0]));
    assert!(attrs::item_attrs(original).inline);
    assert!(
        attrs::item_attrs(original).unsupported.is_empty(),
        "the explicit ordinary inline implementation now owns this directive"
    );
    let filtered = checked.mode_attrs(tcx, local).unwrap();
    assert!(filtered.unsupported.is_empty());
    assert!(modes::local_signature_modes(
        tcx,
        local,
        local,
        Mode::Spec,
        &filtered,
        tcx.def_span(ordered)
    )
    .is_ok());
    assert!(matches!(DeclarationModes::new(tcx).check(local), ModeCheck::Clean(_)),
        "a mode walk may consume supported inline syntax; body visibility, native owner and helper authority still require their separate checks");
    for name in ["exec_inline", "other_attribute"] {
        assert!(
            matches!(inline::capture(tcx, named(tcx, name).expect_local(), work),
            Err(Failure::Unknown(reason))
                if reason == "the native getter attributes are not a supported Spec body")
        );
    }
    assert!(
        matches!(inline::capture(tcx, named(tcx, "malformed_inline").expect_local(), work),
        Err(Failure::Unknown(reason))
            if reason.starts_with("the original helper attribute language is unavailable: "))
    );
}

struct Inspect {
    ran: bool,
}
impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        diagnostics(tcx).unwrap();
        let nominal = named(tcx, "Target");
        let ordered = named(tcx, "ordered");
        let implementation_id = tcx.impl_of_assoc(ordered).unwrap();
        let mut work = Work::new();
        // Actual X/Y declaration parameters are rebased onto A/B; spelling
        // equality is neither necessary nor a source of binder authority.
        assert!(implementation(tcx, nominal, implementation_id, &mut work).is_ok());
        assert!(declaration_policy::check(tcx, nominal)
            .for_owner(tcx, nominal)
            .is_some());
        assert!(declaration_policy::check(tcx, ordered)
            .for_owner(tcx, ordered)
            .is_some());
        assert!(member(tcx, nominal, implementation_id, ordered, &mut work).is_ok());
        inline_controls(tcx, ordered, &mut work);
        assert!(inventory::original(tcx, ordered.as_local().unwrap()));
        let swapped = tcx.impl_of_assoc(named(tcx, "permuted")).unwrap();
        unknown(
            implementation(tcx, nominal, swapped, &mut work),
            "the helper impl does not preserve the native nominal type substitution",
        );
        let specialized = tcx.impl_of_assoc(named(tcx, "specialized")).unwrap();
        unknown(
            implementation(tcx, nominal, specialized, &mut work),
            "the helper impl and nominal have different complete binders",
        );
        unknown(
            member(
                tcx,
                nominal,
                implementation_id,
                named(tcx, "own_generic"),
                &mut work,
            ),
            "the helper does not retain its exact complete impl binder",
        );
        unknown(
            member(tcx, nominal, swapped, ordered, &mut work),
            "the helper does not retain its exact complete impl binder",
        );
        unknown(
            member(
                tcx,
                nominal,
                implementation_id,
                named(tcx, "unrelated"),
                &mut work,
            ),
            "the helper does not retain its exact complete impl binder",
        );
        let constrained = named(tcx, "constrained");
        let constrained_impl = tcx.impl_of_assoc(constrained).unwrap();
        assert!(
            implementation(tcx, nominal, constrained_impl, &mut work).is_ok(),
            "the wrong-bound twin must retain the exact Self substitution"
        );
        unknown(
            member(tcx, nominal, constrained_impl, constrained, &mut work),
            "the helper inherited implementation policy is Unknown",
        );
        let slots = inventory::field_slots(tcx, nominal, &mut work).unwrap();
        assert_eq!(slots.len(), 2);
        assert!(inventory::complete(&slots, &slots).is_ok());
        let mut partial = slots.clone();
        let removed = *partial.iter().next().unwrap();
        partial.remove(&removed);
        unknown(
            inventory::complete(&slots, &partial),
            "the original helper inventory does not cover every enum field",
        );
        let other = inventory::field_slots(tcx, named(tcx, "Other"), &mut work).unwrap();
        partial.insert(*other.iter().next().unwrap());
        assert_eq!(
            partial.len(),
            slots.len(),
            "a count-only guard would accept the wrong owner"
        );
        unknown(
            inventory::complete(&slots, &partial),
            "the original helper inventory does not cover every enum field",
        );
        let mut exhausted = Work { remaining: 0 };
        unknown(
            implementation(tcx, nominal, implementation_id, &mut exhausted),
            "nominal helper work bound was exhausted",
        );
        assert_eq!(exhausted.remaining, 0);
        assert!(work.remaining < Work::new().remaining);
        diagnostics(tcx).unwrap();
        self.ran = true;
        Compilation::Stop
    }
}

#[test]
fn native_full_impl_binders_preserve_substitution_and_parent_identity() {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-helper-binders-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let source = directory.0.join("binders.rs");
    std::fs::write(
        &source,
        r#"#![feature(register_tool)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code)]
#[verus::internal(verus_macro)]
pub enum Target<A, B> { Value(A, B) }
pub enum Other { Value(bool) }
#[verus::internal(verus_macro)]
impl<X, Y> Target<X, Y> {
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    #[verifier::inline]
    pub fn ordered(self) {}
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    pub fn own_generic<P>(self, _value: P) {}
    #[verus::internal(verus_macro)] #[verus::internal(exec)]
    #[verifier::inline]
    pub fn exec_inline(self) {}
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    #[verifier::inline] #[verifier::ext_equal]
    pub fn other_attribute(self) {}
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    #[verifier::inline(false)]
    pub fn malformed_inline(self) {}
}
#[verus::internal(verus_macro)]
impl<X, Y> Target<Y, X> {
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    pub fn permuted(self) {}
}
#[verus::internal(verus_macro)]
impl<X> Target<bool, X> {
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    pub fn specialized(self) {}
}
#[verus::internal(verus_macro)]
impl<X: Copy, Y> Target<X, Y> {
    #[verus::internal(verus_macro)] #[verus::internal(spec)]
    pub fn constrained(self) {}
}
pub fn unrelated() {}
"#,
    )
    .unwrap();
    let args = vec![
        "native-helper-binder-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        source.to_str().unwrap().into(),
    ];
    let mut callback = Inspect { ran: false };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback))
        .expect("the real native binder fixture must compile without diagnostics");
    assert!(callback.ran);
}
