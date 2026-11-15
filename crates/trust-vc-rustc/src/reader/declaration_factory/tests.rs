// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::declaration_alignment::source_bindings::{MetadataInput, PinnedFile};
use alignment::{AuthoredSpan, CommonInputs, DeclarationType, GenericScope, SourceAnchor};
use sha2::{Digest as _, Sha256};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Temp(std::path::PathBuf);

impl Drop for Temp {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn key(crate_id: u64, local: u64) -> NativeKey {
    NativeKey {
        stable_crate_id: crate_id,
        def_path_hash: (u128::from(crate_id) << 64) | u128::from(local),
    }
}

fn view(crate_id: u64, erase: bool) -> View {
    let dependencies = BTreeSet::from([[5; 32]]);
    View {
        common: CommonInputs {
            compiler_sha256: [1; 32],
            source: alignment::source_bindings::SourceIdentity {
                manifest_sha256: [2; 32],
                compatibility: alignment::source_bindings::SourceCompatibility::Applied {
                    recipe_sha256: [7; 32],
                    patch_sha256: [9; 32],
                },
            },
            builtin_artifacts: dependencies.clone(),
            dependency_artifacts: dependencies,
        },
        cfg_sha256: [if erase { 7 } else { 6 }; 32],
        stable_crate_id: crate_id,
        selected_rmeta_sha256: erase.then_some([8; 32]),
        declarations: vec![Declaration {
            key: key(crate_id, 1),
            source: Observation::Observed(SourceAnchor {
                identifier: AuthoredSpan {
                    relative_file: "source.rs".into(),
                    file_sha256: [3; 32],
                    original_file_len: 10,
                    bytes: (1, 3),
                },
                enclosing_declarations: vec![],
            }),
            generics: Observation::Observed(vec![GenericScope {
                parent_count: 0,
                own_type_parameters: vec![],
                has_self: false,
            }]),
            shape: Observation::Observed(DeclarationShape::Function {
                origin: FunctionOrigin::Free,
                inputs: vec![DeclarationType::Bool],
                output: Box::new(DeclarationType::Bool),
            }),
        }],
    }
}

fn requested() -> Candidate {
    Candidate {
        keep: key(1, 1),
        erase: key(2, 1),
    }
}

#[test]
fn distinct_native_keys_require_the_computed_source_signature_pair() {
    let keep = view(1, false);
    let erase = view(2, true);
    let compared = ComparedViews::compare(&keep, &erase).unwrap();
    assert!(compared.declarations(&requested()).is_ok());
    let wrong = Candidate {
        keep: key(1, 1),
        erase: key(2, 2),
    };
    assert!(compared.declarations(&wrong).is_err());
}

#[test]
fn a_matching_native_key_cannot_replace_changed_source_or_signature() {
    let keep = view(1, false);
    for mutation in 0..3 {
        let mut erase = view(2, true);
        match mutation {
            0 => erase.declarations[0].source = Observation::Unknown("missing anchor".into()),
            1 => {
                let Observation::Observed(DeclarationShape::Function { inputs, .. }) =
                    &mut erase.declarations[0].shape
                else {
                    panic!("fixture shape");
                };
                inputs.clear();
            }
            _ => erase.common.compiler_sha256 = [4; 32],
        }
        assert!(ComparedViews::compare(&keep, &erase)
            .and_then(|compared| compared.declarations(&requested()))
            .is_err());
    }
}

#[test]
fn duplicate_authored_counterparts_do_not_select_the_first_declaration() {
    let keep = view(1, false);
    let mut erase = view(2, true);
    let mut duplicate = erase.declarations[0].clone();
    duplicate.key = key(2, 2);
    erase.declarations.push(duplicate);
    assert!(ComparedViews::compare(&keep, &erase)
        .and_then(|compared| compared.declarations(&requested()))
        .is_err());
}

#[test]
fn several_candidates_retain_their_own_source_matched_declarations() {
    let mut keep = view(1, false);
    let mut erase = view(2, true);
    for view in [&mut keep, &mut erase] {
        let mut second = view.declarations[0].clone();
        second.key = key(view.stable_crate_id, 2);
        let Observation::Observed(anchor) = &mut second.source else {
            panic!("fixture source")
        };
        anchor.identifier.bytes = (4, 6);
        view.declarations.push(second);
    }
    erase.declarations.reverse();
    let compared = ComparedViews::compare(&keep, &erase).unwrap();
    assert_eq!(compared.candidates().matches.len(), 2);
    for n in [2, 1, 2] {
        let pair = Candidate {
            keep: key(1, n),
            erase: key(2, n),
        };
        let (actual_keep, actual_erase) = compared.declarations(&pair).unwrap();
        assert_eq!(actual_keep.key, pair.keep);
        assert_eq!(actual_erase.key, pair.erase);
        assert!(keep
            .declarations
            .iter()
            .any(|v| std::ptr::eq(v, actual_keep)));
        assert!(erase
            .declarations
            .iter()
            .any(|v| std::ptr::eq(v, actual_erase)));
        let wrong = Candidate {
            keep: pair.keep,
            erase: key(2, 3 - n),
        };
        assert!(compared.declarations(&wrong).is_err());
    }
    let candidates = compared.into_candidates();
    assert_eq!(candidates.matches.len(), 2);
    assert!(candidates.refused.is_empty());
}

#[test]
fn checked_spec_modes_cannot_admit_proof_exec_or_mutable_parameters() {
    assert!(spec_signature(
        Mode::Spec,
        [(Mode::Spec, false)],
        Mode::Spec
    ));
    for (mode, parameter, mutable, ret) in [
        (Mode::Proof, Mode::Spec, false, Mode::Spec),
        (Mode::Exec, Mode::Spec, false, Mode::Spec),
        (Mode::Spec, Mode::Proof, false, Mode::Spec),
        (Mode::Spec, Mode::Exec, false, Mode::Spec),
        (Mode::Spec, Mode::Spec, true, Mode::Spec),
        (Mode::Spec, Mode::Spec, false, Mode::Proof),
    ] {
        assert!(!spec_signature(mode, [(parameter, mutable)], ret));
    }
}

#[test]
fn identical_artifact_bytes_do_not_merge_distinct_native_target_identities() {
    let temp = Temp(std::env::temp_dir().join(format!(
        "trust-vc-declaration-factory-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&temp.0).unwrap();
    let file = |name: &str, bytes: &[u8]| {
        let path = temp.0.join(name);
        std::fs::write(&path, bytes).unwrap();
        PinnedFile {
            path,
            sha256: Sha256::digest(bytes).into(),
        }
    };
    // These files test byte/identity policy, not genuine metadata semantics.
    let first = file("first.rmeta", b"same bytes");
    let second = file("second.rmeta", b"same bytes");
    let common = file("common.rmeta", b"different dependency bytes");
    let input = |id, file| MetadataInput {
        stable_crate_id: id,
        svh: 9,
        file,
    };
    let dependencies = Metadata::load([input(3, common.clone())]).unwrap();
    let selected = Metadata::load([input(1, first.clone())]).unwrap();
    assert!(target_is_separate(
        &selected,
        &dependencies,
        1,
        first.sha256
    ));
    let extra = Metadata::load([input(1, first.clone()), input(2, second)]).unwrap();
    assert_eq!(extra.digests().len(), 1);
    assert!(!target_is_separate(&extra, &dependencies, 1, first.sha256));
    let reused_id = Metadata::load([input(1, common)]).unwrap();
    assert!(!target_is_separate(&selected, &reused_id, 1, first.sha256));
}
