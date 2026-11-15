// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real native owner/source components, never a fresh macro/helper positive.

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use sha2::{Digest as _, Sha256};

use super::*;
use crate::declaration_alignment::source_bindings::PinnedFile;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
fn digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
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

#[derive(Clone, Copy)]
enum Case {
    Prefix,
    Ownership,
    Unsupported,
}
struct Inspect {
    sources: Sources,
    second: Sources,
    case: Case,
    ran: bool,
}
impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        diagnostics(tcx).unwrap();
        let owner = named(tcx, "Target");
        let mut work = Work::new();
        let header = anchor_sources(tcx, tcx.def_span(owner), &self.sources).unwrap();
        let identifier =
            anchor_sources(tcx, tcx.def_ident_span(owner).unwrap(), &self.sources).unwrap();
        let checked = capture_sources(tcx, owner, &self.sources, &header, &identifier, &mut work)
            .unwrap_or_else(|reason| {
                panic!("source-only native enum component must be available: {reason:?}")
            });
        match self.case {
            Case::Prefix => {
                assert!(checked.current(tcx, &self.sources));
                assert!(checked.extent.bytes.0 < header.bytes.0);
                let text = self.sources.text_for(&checked.extent, 16_384).unwrap();
                assert!(text.starts_with("/// first source doc"));
                assert!(text.ends_with("Value(T) }"));
                assert!(checked.extent.bytes.1 > header.bytes.1);
                assert!(contains(&checked.extent, &header));
                let mut expected_header = header.clone();
                expected_header.bytes.0 = checked.extent.bytes.0;
                assert!(checked.matches_anchors(&expected_header, &checked.extent));
                let mut wrong = expected_header.clone();
                wrong.bytes.1 -= 1;
                assert!(!checked.matches_anchors(&wrong, &checked.extent));
                let mut wrong = checked.extent.clone();
                wrong.bytes.0 -= 1;
                assert!(!checked.matches_anchors(&expected_header, &wrong));
                let mut wrong = checked.extent.clone();
                wrong.file_sha256[0] ^= 1;
                assert!(!checked.matches_anchors(&expected_header, &wrong));
                assert!(self.sources.text_for(&wrong, 16_384).is_err());
                let mut wrong = checked.extent.clone();
                wrong.original_file_len += 1;
                assert!(!checked.matches_anchors(&expected_header, &wrong));
                assert!(self.sources.text_for(&checked.extent, 1).is_err());
                assert!(self.sources.text_for(&wrong, 16_384).is_err());
                let mut wrong = checked.extent.clone();
                wrong.relative_file = "absent.rs".into();
                assert!(self.sources.text_for(&wrong, 16_384).is_err());
                let plain_owner = named(tcx, "Plain");
                let plain_header =
                    anchor_sources(tcx, tcx.def_span(plain_owner), &self.sources).unwrap();
                let plain_identifier =
                    anchor_sources(tcx, tcx.def_ident_span(plain_owner).unwrap(), &self.sources)
                        .unwrap();
                let plain = capture_sources(
                    tcx,
                    plain_owner,
                    &self.sources,
                    &plain_header,
                    &plain_identifier,
                    &mut work,
                )
                .unwrap_or_else(|reason| panic!("{reason:?}"));
                assert_eq!(plain.extent.bytes.0, plain_header.bytes.0);
                let mut unlicensed_prefix = plain.extent.clone();
                unlicensed_prefix.bytes.0 -= 1;
                let mut unlicensed_header = plain_header;
                unlicensed_header.bytes.0 -= 1;
                assert!(
                    !plain.matches_anchors(&unlicensed_header, &unlicensed_prefix),
                    "no independently attached prefix means no extension of either endpoint"
                );
            }
            Case::Ownership => {
                assert!(
                    !checked.current(tcx, &self.second),
                    "equal bytes do not replace the borrowed source snapshot"
                );
                assert!(slot_matches(checked.attributes, 0, &checked.attributes[0]));
                let copied = checked.attributes[0].clone();
                assert!(!slot_matches(checked.attributes, 0, &copied));
                let sibling = named(tcx, "Sibling").expect_local();
                let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(sibling));
                assert!(!slot_matches(checked.attributes, 0, &attributes[0]));
                assert!(capture_sources(
                    tcx,
                    sibling.to_def_id(),
                    &self.sources,
                    &header,
                    &identifier,
                    &mut work
                )
                .is_err());
            }
            Case::Unsupported => {
                for name in ["Representation", "Huge"] {
                    let owner = named(tcx, name);
                    let header = anchor_sources(tcx, tcx.def_span(owner), &self.sources).unwrap();
                    let identifier =
                        anchor_sources(tcx, tcx.def_ident_span(owner).unwrap(), &self.sources)
                            .unwrap();
                    assert!(
                        matches!(
                            capture_sources(
                                tcx,
                                owner,
                                &self.sources,
                                &header,
                                &identifier,
                                &mut work
                            ),
                            Err(Failure::Unknown(_))
                        ),
                        "unsupported native attribute/prefix must remain Unknown"
                    );
                }
                let mut exhausted = Work { remaining: 0 };
                assert!(matches!(
                    capture_sources(
                        tcx,
                        owner,
                        &self.sources,
                        &header,
                        &identifier,
                        &mut exhausted
                    ),
                    Err(Failure::Unknown(_))
                ));
            }
        }
        diagnostics(tcx).unwrap();
        self.ran = true;
        Compilation::Stop
    }
}

fn run(case: Case) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-enum-source-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let root = directory.0.join("source");
    std::fs::create_dir(&root).unwrap();
    let source = root.join("native.rs");
    let prefix = r##"#![feature(register_tool)]
#![register_tool(verifier)]
#![allow(dead_code)]
/// first source doc
// ordinary explanation
#[doc = r#"second source doc ]"#]
/* ordinary /* nested */ explanation */
#[verifier::accept_recursive_types(T)]
pub enum Target<T> { Value(T) }
/// different owner
pub enum Sibling { Value }
pub enum Plain { Value }
#[repr(C)]
pub enum Representation { Value }
"##;
    let contents = format!(
        "{prefix}/// {}\npub enum Huge {{ Value }}\n",
        "x".repeat(PREFIX_BYTES + 1)
    );
    std::fs::write(&source, &contents).unwrap();
    let manifest = directory.0.join("manifest.json");
    let hash = digest(contents.as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    std::fs::write(
        &manifest,
        json!({"files_sha256": {"native.rs": hash}, "symlink_targets": {}}).to_string(),
    )
    .unwrap();
    let pin = PinnedFile {
        path: manifest.clone(),
        sha256: digest(&std::fs::read(&manifest).unwrap()),
    };
    let sources = Sources::load(&root, pin.clone(), None).unwrap();
    let second = Sources::load(&root, pin, None).unwrap();
    let args = vec![
        "native-enum-source-control".into(),
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
    let mut callback = Inspect {
        sources,
        second,
        case,
        ran: false,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback))
        .expect("the actual source-component fixture must compile without diagnostics");
    assert!(callback.ran);
}

#[test]
fn native_original_enum_prefix_and_exact_endpoint_components() {
    run(Case::Prefix);
}
#[test]
fn native_original_enum_attribute_slots_and_source_snapshots_cannot_be_swapped() {
    run(Case::Ownership);
}
#[test]
fn native_unrepresented_attribute_and_bounded_prefix_remain_unknown() {
    run(Case::Unsupported);
}
