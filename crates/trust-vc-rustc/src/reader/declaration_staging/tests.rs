// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use alignment::{
    AuthoredSpan, CommonInputs, Declaration, DeclarationShape, GenericScope, NominalKind,
    SourceAnchor,
};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

#[test]
fn fresh_build_inputs_cannot_borrow_prebuilt_or_receipt_authority() {
    let temp = Temp(std::env::temp_dir().join(format!(
        "trust-vc-build-request-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&temp.0).unwrap();
    for (index, request) in [
        json!({"schema": "trust-vc.native-declaration-staging-request@2", "builtin": {}}),
        json!({"schema": "trust-vc.native-declaration-staging-request@2", "macros": []}),
        json!({"schema": "trust-vc.native-declaration-staging-request@1", "registry_archives": []}),
        json!({"schema": "trust-vc.native-declaration-staging-request@2", "import_authorized": true}),
        json!({"schema": "trust-vc.native-declaration-staging-request@2", "build_receipt": {}}),
    ].into_iter().enumerate() {
        let path = temp.0.join(format!("request{index}.json"));
        std::fs::write(&path, serde_json::to_vec(&request).unwrap()).unwrap();
        let Err(error) = inputs::Inputs::load(&path) else {
            panic!("caller fields cannot construct a native build origin");
        };
        assert!(error.contains("unsupported staging request or authority-bearing"), "{error}");
    }
}

struct Temp(std::path::PathBuf);

impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn view() -> View {
    View {
        common: CommonInputs {
            compiler_sha256: [1; 32],
            source: alignment::source_bindings::SourceIdentity {
                manifest_sha256: [2; 32],
                compatibility: alignment::source_bindings::SourceCompatibility::Applied {
                    recipe_sha256: [7; 32],
                    patch_sha256: [3; 32],
                },
            },
            builtin_artifacts: BTreeSet::from([[4; 32]]),
            dependency_artifacts: BTreeSet::from([[4; 32]]),
        },
        cfg_sha256: [5; 32],
        stable_crate_id: 1,
        selected_rmeta_sha256: None,
        declarations: vec![Declaration {
            key: NativeKey {
                stable_crate_id: 1,
                def_path_hash: (1u128 << 64) | 1,
            },
            source: Observation::Observed(SourceAnchor {
                identifier: AuthoredSpan {
                    relative_file: "library.rs".into(),
                    file_sha256: [6; 32],
                    original_file_len: 20,
                    bytes: (1, 5),
                },
                enclosing_declarations: vec![],
            }),
            generics: Observation::Observed(vec![GenericScope {
                parent_count: 0,
                own_type_parameters: vec![],
                has_self: false,
            }]),
            shape: Observation::Observed(DeclarationShape::Nominal {
                kind: NominalKind::Struct,
            }),
        }],
    }
}

#[test]
fn metadata_roundtrip_requires_the_same_owned_native_declaration() {
    let original = view();
    assert!(roundtrip(&original, &original).unwrap().is_empty());
    let mut loaded = view();
    loaded.declarations[0].key.def_path_hash += 1;
    assert_eq!(roundtrip(&original, &loaded).unwrap().len(), 2);
}

#[test]
fn source_or_type_changes_cannot_borrow_an_emission_fact() {
    for mutation in 0..3 {
        let original = view();
        let mut loaded = view();
        match mutation {
            0 => {
                loaded.declarations[0].source =
                    Observation::Unknown("metadata source unavailable".into())
            }
            1 => {
                loaded.declarations[0].shape = Observation::Observed(DeclarationShape::Nominal {
                    kind: NominalKind::Enum,
                })
            }
            _ => loaded.common.compiler_sha256 = [9; 32],
        }
        if mutation == 2 {
            assert!(roundtrip(&original, &loaded).is_err());
        } else {
            assert_eq!(roundtrip(&original, &loaded).unwrap().len(), 1);
        }
    }
}

#[test]
fn an_unknown_fact_stays_unknown_in_both_native_views() {
    let mut original = view();
    let mut loaded = view();
    original.declarations[0].shape = Observation::Unknown("unsupported local type".into());
    loaded.declarations[0].shape = Observation::Unknown("unsupported imported type".into());
    assert!(roundtrip(&original, &loaded).unwrap().is_empty());
    assert!(matches!(
        loaded.declarations[0].shape,
        Observation::Unknown(_)
    ));
}

#[test]
fn duplicate_native_keys_refuse_the_handoff() {
    let mut duplicate = view();
    duplicate
        .declarations
        .push(duplicate.declarations[0].clone());
    assert!(roundtrip(&duplicate, &view()).is_err());
    assert!(roundtrip(&view(), &duplicate).is_err());
}

#[cfg(unix)]
#[test]
fn output_aliases_cannot_create_inside_the_approved_source_graph() {
    let temp = Temp(std::env::temp_dir().join(format!(
        "trust-vc-stage-output-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&temp.0).unwrap();
    let source = temp.0.join("source");
    std::fs::create_dir(&source).unwrap();
    let canonical = source.canonicalize().unwrap();
    let alias = temp.0.join("source-alias");
    std::os::unix::fs::symlink(&canonical, &alias).unwrap();
    assert!(inputs::canonical_output(&alias.join("new-output"), &canonical).is_err());
    if let Ok(relative) = canonical.strip_prefix("/private/tmp") {
        let raw_tmp_alias = Path::new("/tmp").join(relative).join("new-output");
        assert!(!raw_tmp_alias.starts_with(&canonical));
        assert!(inputs::canonical_output(&raw_tmp_alias, &canonical).is_err());
    }
    assert!(!source.join("new-output").exists());
    let safe = inputs::canonical_output(&temp.0.join("safe-output"), &canonical).unwrap();
    assert_eq!(safe, temp.0.canonicalize().unwrap().join("safe-output"));
    let dangling = temp.0.join("dangling-output");
    std::os::unix::fs::symlink(temp.0.join("not-present"), &dangling).unwrap();
    assert!(!dangling.exists());
    assert!(inputs::canonical_output(&dangling, &canonical).is_err());
}

#[test]
fn actual_native_compiler_image_is_separate_from_the_producer_executable() {
    let compiler = identity::loaded_driver().unwrap();
    let producer = std::env::current_exe().unwrap().canonicalize().unwrap();
    assert_ne!(compiler.path, producer);
    compiler.read().unwrap();
    assert_eq!(identity::loaded_driver_path().unwrap(), compiler.path);
}
