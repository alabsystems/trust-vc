// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native observation components; no fresh macro/helper permission is created.

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

struct Inspect {
    ran: bool,
}
impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        diagnostics(tcx).unwrap();
        let target = named(tcx, "Target");
        let observed = capture(tcx, target, &mut Budget::new()).unwrap();
        assert_eq!(observed["owner"], key(tcx, target));
        assert_eq!(observed["original_item_owner"], observed["owner"]);
        assert_eq!(observed["root_hir_owner"], observed["owner"]);
        assert_eq!(observed["root_hir_local_index"], 0);
        assert_eq!(observed["original_item_pointer_matches_current"], true);
        assert_eq!(
            observed["original_root_slice_pointer_matches_hir_attrs"],
            true
        );
        assert_eq!(observed["original_root_attribute_count"], 3);
        assert_eq!(observed["current_root_attribute_count"], 3);
        let rows = observed["inventory"]["slots"].as_array().unwrap();
        assert_eq!(rows.len(), 3);
        assert!(rows
            .iter()
            .all(|row| row["original_reference_matches_current_slot"] == true));
        assert!(rows.iter().all(|row| row["detail"]["style"] == "Outer"));
        assert_eq!(
            rows.iter()
                .filter(|row| row["detail"]["kind"] == "ParsedDocComment")
                .count(),
            2
        );
        assert_eq!(
            rows.iter()
                .filter(|row| row["detail"]["doc_kind"] == "RawDocAttribute")
                .count(),
            1
        );
        assert_eq!(
            rows.iter()
                .filter(|row| row["detail"]["doc_kind"] == "SugaredDocComment")
                .count(),
            1
        );
        let tool = rows
            .iter()
            .find(|row| row["detail"]["kind"] == "Tool")
            .unwrap();
        assert_eq!(
            tool["detail"]["path_observation"]["segments"],
            json!(["verifier", "accept_recursive_types"])
        );
        assert!(tool["detail"]["native_attr_id"].is_null());
        assert_eq!(
            tool["detail"]["native_attr_id_state"],
            "not retained for this native kind"
        );
        assert_eq!(
            tool["detail"]["argument_observation"]["top_level_token_count"],
            1
        );
        let header = tcx.def_span(target);
        let file = tcx.sess.source_map().lookup_source_file(header.lo());
        let header_lo = file.original_relative_byte_pos(header.lo()).to_u32();
        for row in rows {
            let source = &row["detail"]["native_span"]["native"];
            assert_eq!(source["state"], "ObservedCompilerSourceCoordinates");
            assert!(source["original_lo"].as_u64().unwrap() < u64::from(header_lo));
            assert!(source["original_hi"].as_u64().unwrap() <= u64::from(header_lo));
            assert_eq!(source["source_binding_authority"], false);
        }
        let raw = tcx.lower_to_hir(target.expect_local()).as_owner().unwrap();
        let id = tcx.local_def_id_to_hir_id(target.expect_local());
        let original = raw.attrs.get(id.local_id);
        let attribute = original
            .iter()
            .find(|attribute| matches!(attribute, Attribute::Tool(_)))
            .unwrap();
        let copy = (*attribute).clone();
        let (Attribute::Tool(a), Attribute::Tool(b)) = (attribute, &copy) else {
            unreachable!()
        };
        assert_eq!(a.path.segments, b.path.segments);
        assert_eq!(a.span, b.span);
        assert!(!same_attribute(attribute, Some(&copy)));
        let other = named(tcx, "Other");
        let other_observation = capture(tcx, other, &mut Budget::new()).unwrap();
        assert_ne!(other_observation["owner"], observed["owner"]);
        assert_eq!(other_observation["original_root_attribute_count"], 0);
        let many = capture(tcx, named(tcx, "Many"), &mut Budget::new()).unwrap();
        assert_eq!(many["original_root_attribute_count"], ATTRIBUTES + 1);
        assert_eq!(many["inventory"]["state"], "Unknown");
        assert_eq!(many["source_extent_authorized"], false);
        assert_eq!(many["helper_authorized"], false);
        diagnostics(tcx).unwrap();
        self.ran = true;
        Compilation::Stop
    }
}

#[test]
fn native_root_attributes_preserve_real_ownership_style_and_coordinates() {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-helper-attribute-context-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let source = directory.0.join("attributes.rs");
    let many = "#[verifier::marker]\n".repeat(ATTRIBUTES + 1);
    std::fs::write(
        &source,
        format!(
            r#"#![feature(register_tool)]
#![register_tool(verifier)]
#![allow(dead_code)]
#[doc = "raw documentation"]
/// Sugared documentation.
#[verifier::accept_recursive_types(A)]
pub enum Target<A> {{ Value(A) }}
pub enum Other {{ Value }}
{many}
pub enum Many {{ Value }}
"#
        ),
    )
    .unwrap();
    let args = vec![
        "native-helper-attribute-context-control".into(),
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
        .expect("the real native attribute fixture must analyze without errors");
    assert!(callback.ran);
}
