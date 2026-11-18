//! Native observations of a rejection-only predicate. The syntax markers in
//! this Rust fixture do not authenticate a helper cohort or construct a
//! ClosedScope, SourceNominals, source family, or import capability.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;

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

#[derive(Default)]
struct Capture {
    observed: bool,
}

impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let owners: BTreeMap<_, _> = tcx
            .hir_crate_items(())
            .owners()
            .filter_map(|owner| {
                let definition = owner.def_id;
                tcx.opt_item_name(definition.to_def_id())
                    .map(|name| (name.to_string(), definition))
            })
            .collect();
        for (name, rejected) in [
            ("Eligible", false),
            ("Private", true),
            ("Zero", true),
            ("Two", true),
            ("Defaulted", true),
            ("Unsized", true),
            ("Spec", true),
            ("Proof", true),
            ("Transparent", true),
            ("Unknown", true),
            ("MissingRecursion", true),
            ("Enumeration", true),
            ("Function", true),
        ] {
            let owner = *owners.get(name).expect("the actual native fixture owner");
            let key = declaration_native::key(tcx, owner.to_def_id());
            let checked = declaration_policy::check(tcx, owner.to_def_id());
            let policy = checked.for_owner(tcx, owner.to_def_id());
            let observation = checked.observation();
            if matches!(name, "Unknown" | "MissingRecursion") {
                assert!(policy.is_none(), "{name}: {observation}");
                assert_eq!(observation["state"], "Unknown");
                if name == "MissingRecursion" {
                    assert_eq!(
                        observation["reason"],
                        "external_body needs an explicit recursion policy for every type parameter",
                    );
                }
            } else {
                assert!(policy.is_some(), "known native policy for {name}: {observation}");
            }
            let reason = unsupported_shape(tcx, Some(owner), key, policy);
            assert_eq!(
                reason.is_some(),
                rejected,
                "actual native declaration {name}: {reason:?}; {observation}",
            );
        }
        let owner = owners["Eligible"];
        let other = owners["Two"];
        let key = declaration_native::key(tcx, owner.to_def_id());
        let checked = declaration_policy::check(tcx, owner.to_def_id());
        let policy = checked.for_owner(tcx, owner.to_def_id()).unwrap();
        let nominal = policy.nominal().unwrap();
        let attributes = crate::reader::attrs::item_attrs(
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
        );
        assert!(attributes.verus_macro && attributes.external_body);
        assert_eq!(policy.owner(), key);
        assert_eq!(policy.parameters().len(), 1);
        assert_eq!(policy.parameters()[0].index, 0);
        assert!(!policy.parameters()[0].has_default);
        assert!(nominal.known_sized() && nominal.external_body());
        assert_eq!(nominal.mode(), trust_vc_vcir::Mode::Exec);
        assert_eq!(nominal.recursion().len(), 1);
        let other_checked = declaration_policy::check(tcx, other.to_def_id());
        let other_policy = other_checked.for_owner(tcx, other.to_def_id()).unwrap();
        assert!(unsupported_shape(tcx, None, key, Some(policy)).is_some());
        assert!(unsupported_shape(tcx, Some(other), key, Some(policy)).is_some());
        assert!(unsupported_shape(tcx, Some(owner), key, Some(other_policy)).is_some());
        assert!(unsupported_shape(tcx, Some(owner), key, None).is_some());
        // None is only the absence of an early rejection. The test never
        // creates a native cohort or calls any admission/installation API.
        assert!(unsupported_shape(tcx, Some(owner), key, Some(policy)).is_none());
        self.observed = true;
        Compilation::Stop
    }
}

#[test]
fn native_nominal_preflight_rejects_only_definitely_unsupported_shapes() {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-source-nominal-preflight-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let path = directory.0.join("preflight.rs");
    std::fs::write(
        &path,
        r#"#![feature(register_tool)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case)]
use std::marker::PhantomData;
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)]
pub struct Eligible<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)]
struct Private<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
pub struct Zero;
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)] #[verifier::reject_recursive_types(B)]
pub struct Two<A, B> { value: PhantomData<(A, B)> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)]
pub struct Defaulted<A = bool> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)]
pub struct Unsized<A: ?Sized> { value: A }
#[verus::internal(verus_macro)] #[verus::internal(external_body)] #[verus::internal(spec)]
#[verifier::reject_recursive_types(A)]
pub struct Spec<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)] #[verus::internal(proof)]
#[verifier::reject_recursive_types(A)]
pub struct Proof<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)]
pub struct Transparent<A> { value: PhantomData<A> }
pub struct Unknown<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
pub struct MissingRecursion<A> { value: PhantomData<A> }
#[verus::internal(verus_macro)] #[verus::internal(external_body)]
#[verifier::reject_recursive_types(A)]
pub enum Enumeration<A> { Value(A) }
#[verus::internal(verus_macro)]
pub fn Function<A>(value: A) -> A { value }
"#,
    )
    .unwrap();
    let arguments = vec![
        "native-source-nominal-preflight-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_source_nominal_preflight_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ];
    let mut capture = Capture::default();
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut capture))
        .expect("the ordinary native rejection-only fixture must compile");
    assert!(capture.observed, "the genuine native analysis callback ran");
}
