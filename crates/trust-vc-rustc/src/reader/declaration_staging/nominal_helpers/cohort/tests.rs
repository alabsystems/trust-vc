// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real selected foreign metadata cannot replace fresh source construction.
//! This refusal fixture never stands for an approved macro/helper positive.

extern crate rustc_driver;

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use super::*;
use crate::declaration_alignment::source_bindings::{MetadataInput, PinnedFile, Sources};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn pin(path: PathBuf) -> PinnedFile {
    let path = path.canonicalize().unwrap();
    PinnedFile {
        sha256: inputs::digest(&path).unwrap(),
        path,
    }
}

fn arguments(path: &Path, output: &Path, name: &str) -> Vec<String> {
    vec![
        "native-helper-cohort-control".into(),
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

fn cross_file_authored_control(tcx: TyCtxt<'_>, inputs: &Inputs) {
    let nominal = tcx
        .hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id.to_def_id())
        .find(|owner| {
            tcx.opt_item_name(*owner)
                .is_some_and(|name| name.as_str() == "CrossFile")
        })
        .unwrap();
    let implementations = tcx.inherent_impls(nominal);
    let [implementation] = implementations else {
        panic!("the distinct-file source control must have exactly one inherent implementation");
    };
    let implementation = *implementation;
    assert!(inventory::original(tcx, nominal.expect_local()));
    assert!(inventory::original(tcx, implementation.expect_local()));
    assert_eq!(tcx.generics_of(nominal).own_params.len(), 1);
    assert_eq!(tcx.generics_of(implementation).own_params.len(), 1);
    // This uses the real normalized Self substitution and full native binder;
    // source disjointness alone never supplies their correspondence.
    assert!(types::implementation(tcx, nominal, implementation, &mut Work::new()).is_ok());
    let raw = tcx
        .lower_to_hir(implementation.expect_local())
        .as_owner()
        .unwrap();
    let rustc_hir::OwnerNode::Item(item) = raw.node() else {
        unreachable!()
    };
    let rustc_hir::ItemKind::Impl(original) = &item.kind else {
        unreachable!()
    };
    let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, path)) = &original.self_ty.kind
    else {
        panic!("the distinct-file control must retain its actual Self path");
    };
    assert!(
        matches!(path.res, rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Struct, actual)
        if actual == nominal)
    );
    let nominal_span = origin::anchor(tcx, tcx.def_span(nominal), inputs).unwrap();
    let nominal_ident = origin::anchor(tcx, tcx.def_ident_span(nominal).unwrap(), inputs).unwrap();
    let header = origin::anchor(tcx, tcx.def_span(implementation), inputs).unwrap();
    let full = origin::anchor(tcx, item.span, inputs).unwrap();
    let self_ident = origin::anchor(tcx, path.segments.last().unwrap().ident.span, inputs).unwrap();
    assert_ne!(nominal_span.relative_file, header.relative_file);
    assert_eq!(nominal_span.relative_file, "separate.rs");
    assert_eq!(header.relative_file, "client.rs");
    assert!(origin::authored(&header, &nominal_span, &self_ident));
    assert!(origin::authored(&full, &nominal_span, &self_ident));
    assert!(origin::contains(&full, &header));
    assert!(
        !origin::authored(&header, &nominal_span, &nominal_ident),
        "a distinct source file cannot supply the impl's own Self identifier"
    );
    let [member] = original.items else {
        panic!("the distinct-file impl must have one authored member");
    };
    let member = member.owner_id.def_id;
    assert_eq!(tcx.impl_of_assoc(member.to_def_id()), Some(implementation));
    assert!(inventory::original(tcx, member));
    let member_span = origin::anchor(tcx, tcx.def_span(member), inputs).unwrap();
    assert!(origin::contains(&full, &member_span));
    assert!(!origin::contains(&header, &member_span));
}

struct Emit;
impl Callbacks for Emit {}
struct Inspect {
    directory: PathBuf,
    source: PathBuf,
    ran: bool,
}
impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        diagnostics(tcx).unwrap();
        let marker = tcx
            .get_diagnostic_item(Symbol::intern("verus::verus_builtin::get_variant_field"))
            .unwrap();
        assert!(!marker.is_local());
        let mut common_files = BTreeMap::new();
        let mut selected = Vec::new();
        for krate in tcx.crates(()) {
            let source = tcx.used_crate_source(*krate);
            let file = pin(source
                .rmeta
                .as_ref()
                .or(source.rlib.as_ref())
                .or(source.dylib.as_ref())
                .unwrap()
                .to_path_buf());
            common_files.insert(file.path.clone(), file.clone());
            selected.push(MetadataInput {
                stable_crate_id: tcx.stable_crate_id(*krate).as_u64(),
                svh: tcx.crate_hash(*krate).as_u128(),
                file,
            });
        }
        let metadata = Metadata::load(selected).unwrap();
        let mut source_hashes = BTreeMap::new();
        for name in ["client.rs", "separate.rs"] {
            let file = pin(self.source.parent().unwrap().join(name));
            source_hashes.insert(
                name,
                file.sha256
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<String>(),
            );
        }
        let manifest = self.directory.join("manifest.json");
        std::fs::write(&manifest, serde_json::to_vec(&json!({
            "git_commit": "native-counterfeit-helper-control", "archive_sha256": "00".repeat(32),
            "files_sha256": source_hashes, "symlink_targets": {}
        })).unwrap()).unwrap();
        let sources = Sources::load(self.source.parent().unwrap(), pin(manifest), None).unwrap();
        let native = tcx.used_crate_source(marker.krate);
        let builtin = pin(native
            .rmeta
            .as_ref()
            .or(native.rlib.as_ref())
            .or(native.dylib.as_ref())
            .unwrap()
            .to_path_buf());
        let inputs = Inputs {
            sources,
            common_files,
            builtin,
            macros: vec![],
            output: self.directory.join("unused-output"),
            producer_sha256: inputs::digest(&std::env::current_exe().unwrap()).unwrap(),
            compiler_driver: identity::loaded_driver().unwrap(),
            build_origin: None,
        };
        let nominal = tcx
            .hir_crate_items(())
            .owners()
            .map(|owner| owner.def_id.to_def_id())
            .find(|owner| {
                tcx.opt_item_name(*owner)
                    .is_some_and(|name| name.as_str() == "Target")
            })
            .unwrap();
        let implementations = tcx.inherent_impls(nominal);
        assert_eq!(implementations.len(), 1);
        let implementation = implementations[0];
        assert_eq!(
            tcx.expn_that_defined(nominal),
            tcx.expn_that_defined(implementation),
            "the native source control must exercise two items from the SAME macro event"
        );
        let raw = tcx
            .lower_to_hir(implementation.expect_local())
            .as_owner()
            .unwrap();
        let rustc_hir::OwnerNode::Item(item) = raw.node() else {
            unreachable!()
        };
        let rustc_hir::ItemKind::Impl(original) = &item.kind else {
            unreachable!()
        };
        let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, path)) =
            &original.self_ty.kind
        else {
            panic!("the actual authored Self path must be represented");
        };
        let nominal_span = origin::anchor(tcx, tcx.def_span(nominal), &inputs).unwrap();
        let nominal_ident =
            origin::anchor(tcx, tcx.def_ident_span(nominal).unwrap(), &inputs).unwrap();
        let impl_span = origin::anchor(tcx, tcx.def_span(implementation), &inputs).unwrap();
        let full_impl_span = origin::anchor(tcx, item.span, &inputs).unwrap();
        let self_ident =
            origin::anchor(tcx, path.segments.last().unwrap().ident.span, &inputs).unwrap();
        assert!(origin::authored(&impl_span, &nominal_span, &self_ident));
        assert!(origin::authored(
            &full_impl_span,
            &nominal_span,
            &self_ident
        ));
        assert!(origin::contains(&full_impl_span, &impl_span));
        assert!(inventory::original(tcx, implementation.expect_local()));
        let [member] = original.items else {
            panic!("the source control must have one authored member");
        };
        let member = member.owner_id.def_id;
        assert_eq!(tcx.impl_of_assoc(member.to_def_id()), Some(implementation));
        assert!(inventory::original(tcx, member));
        let member_span = origin::anchor(tcx, tcx.def_span(member), &inputs).unwrap();
        assert!(
            origin::contains(&full_impl_span, &member_span),
            "the original item span includes its actual authored member"
        );
        assert!(
            !origin::contains(&impl_span, &member_span),
            "the native impl definition span is only the header"
        );
        assert!(!origin::authored(&impl_span, &nominal_span, &nominal_ident));
        assert!(!origin::authored(
            &nominal_span,
            &nominal_span,
            &nominal_ident
        ));
        // These are deliberately invalid data twins, not bound source facts.
        // A same-path digest/length mismatch must not become "another file".
        let mut wrong_digest = nominal_span.clone();
        wrong_digest.file_sha256[0] ^= 1;
        assert!(!origin::authored(&impl_span, &wrong_digest, &self_ident));
        let mut wrong_length = nominal_span.clone();
        wrong_length.original_file_len += 1;
        assert!(!origin::authored(&impl_span, &wrong_length, &self_ident));
        cross_file_authored_control(tcx, &inputs);
        let mut work = Work::new();
        match Cohort::capture(tcx, &inputs, &metadata, &mut work) {
            Err(Failure::Unknown(reason)) => assert_eq!(
                reason,
                "nominal helpers require an actual fresh builtin construction"
            ),
            _ => panic!("selected counterfeit metadata must not create a helper cohort"),
        }
        assert_eq!(
            work.remaining,
            Work::new().remaining,
            "missing source construction declines before field permission or helper work"
        );
        diagnostics(tcx).unwrap();
        self.ran = true;
        Compilation::Stop
    }
}

#[test]
fn native_selected_field_intrinsic_without_fresh_build_cannot_create_helper_facts() {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-helper-cohort-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("foreign.rs");
    std::fs::write(
        &foreign,
        r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::get_variant_field"]
pub fn get_variant_field<A, F>(_value: A, _variant: &str, _field: &str) -> F { loop {} }
"#,
    )
    .unwrap();
    rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&foreign, &directory.0, "counterfeit_helper_fixture"),
            &mut Emit,
        )
    })
    .unwrap();
    let source_root = directory.0.join("source");
    std::fs::create_dir(&source_root).unwrap();
    let source = source_root.join("client.rs");
    std::fs::write(
        source_root.join("separate.rs"),
        "pub struct CrossFile<A>(pub A);\n",
    )
    .unwrap();
    std::fs::write(
        &source,
        r#"mod separate;
impl<A> separate::CrossFile<A> {
    pub fn cross_file_authored(self) {}
}
macro_rules! authored_items {
    ($nominal:item $implementation:item) => { $nominal $implementation };
}
authored_items! {
    pub enum Target { Value(bool) }
    impl Target {
        pub fn authored(self) {}
    }
}
pub fn read(value: Target) -> bool {
    counterfeit_helper_fixture::get_variant_field(value, "Value", "0")
}
"#,
    )
    .unwrap();
    let mut args = arguments(&source, &directory.0, "helper_cohort_client");
    args.extend([
        "--extern".into(),
        format!(
            "counterfeit_helper_fixture={}",
            directory
                .0
                .join("libcounterfeit_helper_fixture.rmeta")
                .display()
        ),
    ]);
    let mut callback = Inspect {
        directory: directory.0.clone(),
        source,
        ran: false,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback)).unwrap();
    assert!(callback.ran);
}
