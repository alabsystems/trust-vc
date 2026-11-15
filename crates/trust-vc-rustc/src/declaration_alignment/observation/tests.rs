// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};

use serde_json::{json, Value};

use super::*;

fn definition(krate: u64, item: u64, kind: NativeDeclarationKind) -> Value {
    json!({"stable_crate_id": format!("{krate:016x}"),
        "def_path_hash": format!("{krate:016x}{item:016x}"),
        "declaration_kind": kind.machine_name(), "kind_debug": "diagnostic only"})
}

fn anchor(lo: u32, hi: u32) -> Value {
    json!({"state": "ObservedRealSourceAnchor", "local_path": "/approved/source.rs",
        "compiler_source_hash": "md5=recorded-native-hash", "original_file_len": 100,
        "original_lo": lo, "original_hi": hi})
}

fn scope(owner: &Value, parent: Option<&Value>, has_parameter: bool) -> Value {
    let parameters = if has_parameter {
        vec![json!({"kind": "Type", "index": 0,
        "has_default": false, "synthetic": false, "pure_wrt_drop": false})]
    } else {
        vec![]
    };
    json!({"definition": owner, "generics": {"parent": parent,
        "parent_count": if parent.is_some() { 1 } else { 0 },
        "has_self": false, "own_parameters": parameters}})
}

fn adt(definition: &Value, arguments: Vec<Value>) -> Value {
    json!({"kind": "Adt", "definition": definition,
        "native_type_parameter_count": arguments.len(), "type_arguments": arguments})
}

/// Like the actual Set/len observations: nominal Param0 carrier, an inherent
/// generic parent, no method-owned slots, and an external nat codomain. These
/// synthetic records test the decoder; their contexts confer no authority.
fn input(krate: u64, erase: bool) -> (Context, Value) {
    let nominal = definition(krate, 1, NativeDeclarationKind::Struct);
    let implementation = definition(krate, 2, NativeDeclarationKind::InherentImplementation);
    let function = definition(krate, 3, NativeDeclarationKind::AssociatedFunction);
    let nat = definition(7, 4, NativeDeclarationKind::Struct);
    let parameter = json!({"kind": "TypeParameter", "index": 0});
    let self_type = adt(&nominal, vec![parameter]);
    let mut nominal_definition = nominal.clone();
    nominal_definition["identifier_anchor"] = anchor(1, 4);
    let mut function_definition = function.clone();
    function_definition["identifier_anchor"] = anchor(5, 8);
    let enclosing = json!({"state": "ObservedAuthoredScopeCandidates", "scopes": []});
    let mut source_anchors = BTreeMap::new();
    for (lo, hi) in [(1, 4), (5, 8), (9, 12)] {
        source_anchors.insert(
            ObservedAnchor {
                local_path: "/approved/source.rs".into(),
                compiler_source_hash: "md5=recorded-native-hash".into(),
                original_file_len: 100,
                bytes: (lo, hi),
            },
            AuthoredSpan {
                relative_file: "source.rs".into(),
                file_sha256: [9; 32],
                original_file_len: 100,
                bytes: (lo, hi),
            },
        );
    }
    let external = ExternalType {
        artifact_sha256: [5; 32],
        key: key(&nat).unwrap(),
        type_parameters: 0,
    };
    let context = Context {
        common: CommonInputs {
            compiler_sha256: [1; 32],
            source: crate::declaration_alignment::source_bindings::SourceIdentity {
                manifest_sha256: [2; 32],
                compatibility:
                    crate::declaration_alignment::source_bindings::SourceCompatibility::Applied {
                        recipe_sha256: [7; 32],
                        patch_sha256: [3; 32],
                    },
            },
            builtin_artifacts: BTreeSet::from([[4; 32]]),
            dependency_artifacts: BTreeSet::from([[4; 32], [5; 32]]),
        },
        cfg_sha256: [if erase { 8 } else { 6 }; 32],
        stable_crate_id: krate,
        selected_rmeta_sha256: erase.then_some([10; 32]),
        source_anchors,
        external_nominals: BTreeMap::from([(external.key, external)]),
    };
    let value = json!({
        "schema": if erase { "trust-vc.erase-declaration-observation@2" } else { "trust-vc.keep-declaration-observation@2" },
        "stable_crate_id": format!("{krate:016x}"), "import_authorized": false, "verified_functions": null,
        "types": [{"definition": nominal_definition, "authored_scope_anchors": enclosing,
            "structural_nominal_type": {"state": "ObservedStructuralNominalType",
                "generic_scopes": [scope(&nominal, None, true)], "type": self_type}}],
        "rows": [{"definition": function_definition,
            "authored_scope_anchors": {"state": "ObservedAuthoredScopeCandidates",
                "scopes": [{"kind": "Impl { of_trait: false }", "definition_anchor": anchor(9, 12)}]},
            "verus_macro_marker_observed": !erase,
            "signature_modes": {"state": "Unknown"}, "header_authority": {"state": "Unknown"},
            "function_container": {"state": "ObservedInherentDeclaration", "parent": implementation,
                "structural_self_type": {"state": "ObservedStructuralNominalType",
                    "generic_scopes": [scope(&implementation, None, true)], "type": self_type}},
            "structural_signature": {"state": "ObservedStructuralSignature", "abi": "Rust",
                "safety": "Safe", "c_variadic": false, "splatted": false,
                "generic_scopes": [scope(&function, Some(&implementation), false), scope(&implementation, None, true)],
                "inputs": [self_type], "output": adt(&nat, vec![])}}],
    });
    (context, value)
}

#[test]
fn actual_shape_fields_correlate_without_equal_native_keys_or_erase_marker() {
    let (context, value) = input(1, false);
    let keep = decode(context, &value).unwrap();
    let (context, value) = input(2, true);
    let erase = decode(context, &value).unwrap();
    let result = super::super::compare(&keep, &erase).unwrap();
    assert_eq!(result.matches.len(), 2);
    assert!(result.refused.is_empty());
}

#[test]
fn missing_source_binding_never_falls_back_to_display_or_equal_hash() {
    let (context, value) = input(1, false);
    let keep = decode(context, &value).unwrap();
    let (mut context, mut value) = input(1, true);
    context
        .source_anchors
        .retain(|coordinates, _| coordinates.bytes != (5, 8));
    value["rows"][0]["definition"]["path_display_only"] = json!("vstd::set::Set::len");
    let erase = decode(context, &value).unwrap();
    assert!(matches!(
        erase.declarations[1].source,
        Observation::Unknown(_)
    ));
    let result = super::super::compare(&keep, &erase).unwrap();
    assert_eq!(result.matches.len(), 1);
    assert_eq!(result.refused.len(), 1);
}

#[test]
fn parent_identity_and_parameter_indices_are_preserved() {
    let (context, value) = input(1, false);
    let keep = decode(context, &value).unwrap();
    for parent_mismatch in [false, true] {
        let (context, mut value) = input(2, true);
        if parent_mismatch {
            value["rows"][0]["function_container"]["parent"] =
                definition(2, 99, NativeDeclarationKind::InherentImplementation);
        } else {
            value["rows"][0]["structural_signature"]["inputs"][0]["type_arguments"][0]["index"] =
                json!(1);
        }
        let erase = decode(context, &value).unwrap();
        let result = super::super::compare(&keep, &erase).unwrap();
        assert_eq!(result.matches.len(), 1);
        assert_eq!(result.refused.len(), 1);
    }
}

#[test]
fn external_nominals_require_actual_artifact_and_binder_observations() {
    for missing_artifact in [false, true] {
        let (mut context, value) = input(2, true);
        if missing_artifact {
            context.common.dependency_artifacts.clear();
        } else {
            context.external_nominals.clear();
        }
        let view = decode(context, &value).unwrap();
        assert!(matches!(
            view.declarations[1].shape,
            Observation::Unknown(_)
        ));
    }
    let (mut context, value) = input(2, true);
    context
        .external_nominals
        .values_mut()
        .next()
        .unwrap()
        .type_parameters = 1;
    assert!(matches!(
        decode(context, &value).unwrap().declarations[1].shape,
        Observation::Unknown(_)
    ));
}

#[test]
fn unsupported_signatures_and_generic_slots_remain_in_the_inventory() {
    for generic in [false, true] {
        let (context, mut value) = input(2, true);
        if generic {
            value["rows"][0]["structural_signature"]["generic_scopes"][1]["generics"]
                ["own_parameters"][0]["kind"] = json!("Const");
        } else {
            value["rows"][0]["structural_signature"]["output"] =
                json!({"kind": "Debug", "value": "nat"});
        }
        let view = decode(context, &value).unwrap();
        assert_eq!(view.declarations.len(), 2);
        assert!(matches!(
            view.declarations[1].shape,
            Observation::Unknown(_)
        ));
    }
}

#[test]
fn unknown_trait_container_does_not_borrow_empty_headers_or_modes() {
    let (context, mut value) = input(2, true);
    value["rows"][0]["function_container"] = json!({"state": "Unknown"});
    value["rows"][0]["header_authority"] = json!({"state": "KnownEmpty"});
    value["rows"][0]["signature_modes"] = json!({"state": "ResolvedLocalDeclarationModes"});
    let view = decode(context, &value).unwrap();
    assert!(matches!(
        view.declarations[1].shape,
        Observation::Unknown(_)
    ));
}

#[test]
fn malformed_view_keys_and_claimed_authority_fail_the_decode() {
    for corruption in 0..6 {
        let (context, mut value) = input(2, true);
        match corruption {
            0 => value["import_authorized"] = json!(true),
            1 => {
                value.as_object_mut().unwrap().remove("verified_functions");
            }
            2 => value["rows"][0]["definition"]["stable_crate_id"] = json!("0000000000000003"),
            3 => {
                let duplicate = value["rows"][0].clone();
                value["rows"].as_array_mut().unwrap().push(duplicate);
            }
            4 => value["schema"] = json!("trust-vc.keep-declaration-observation@2"),
            _ => value["schema"] = json!("trust-vc.erase-declaration-observation@1"),
        }
        assert!(decode(context, &value).is_err());
    }
}

#[test]
fn source_coordinate_binding_cannot_change_the_recorded_range() {
    let (mut context, value) = input(2, true);
    let bound = context
        .source_anchors
        .iter_mut()
        .find(|(coordinates, _)| coordinates.bytes == (5, 8))
        .unwrap()
        .1;
    bound.bytes = (5, 9);
    let view = decode(context, &value).unwrap();
    assert!(matches!(
        view.declarations[1].source,
        Observation::Unknown(_)
    ));
}

#[test]
fn external_inventory_uses_native_binders_and_actual_selected_artifacts() {
    let (context, mut value) = input(2, true);
    let selected = BTreeMap::from([(7, [5; 32])]);
    let inventory = external_nominals(&value, 2, &selected).unwrap();
    assert_eq!(inventory, context.external_nominals);
    assert!(external_nominals(&value, 2, &BTreeMap::new()).is_err());
    value["rows"][0]["structural_signature"]["output"]
        .as_object_mut()
        .unwrap()
        .remove("native_type_parameter_count");
    assert!(external_nominals(&value, 2, &selected).is_err());
}

#[test]
fn machine_declaration_kind_never_uses_debug_spelling() {
    let (context, mut value) = input(2, true);
    value["rows"][0]["function_container"]["parent"]["kind_debug"] = json!("unrelated text");
    assert!(matches!(
        decode(context, &value).unwrap().declarations[1].shape,
        Observation::Observed(_)
    ));
    let (context, mut value) = input(2, true);
    value["rows"][0]["function_container"]["parent"]["kind_debug"] =
        json!("Impl { of_trait: false }");
    value["rows"][0]["function_container"]["parent"]["declaration_kind"] =
        json!("TraitImplementation");
    assert!(matches!(
        decode(context, &value).unwrap().declarations[1].shape,
        Observation::Unknown(_)
    ));
}
