//! Visibility regression for hidden protocol bridge carrier structs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fs;
use std::path::PathBuf;

use syn::{Item, ItemStruct, Visibility};

fn verification_bridge_source_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/verification_bridge_protocol.rs")
}

fn find_named_struct<'a>(items: &'a [Item], name: &str) -> &'a ItemStruct {
    items
        .iter()
        .find_map(|item| match item {
            Item::Struct(item_struct) if item_struct.ident == name => Some(item_struct),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!("expected to find struct {name} in verification_bridge_protocol.rs")
        })
}

fn assert_pub_crate(visibility: &Visibility, item_name: &str) {
    match visibility {
        Visibility::Restricted(restricted) if restricted.path.is_ident("crate") => {}
        _ => panic!("{item_name} should use pub(crate) visibility"),
    }
}

#[test]
fn test_hidden_protocol_bridge_carriers_remain_pub_crate() {
    let source = fs::read_to_string(verification_bridge_source_path())
        .expect("should read verification_bridge.rs");
    let parsed = syn::parse_file(&source).expect("should parse verification_bridge.rs");

    for struct_name in [
        "ProtocolStateVarDef",
        "ProtocolActionDef",
        "ProtocolInvariantDef",
        "ProtocolLivenessDef",
    ] {
        let item = find_named_struct(&parsed.items, struct_name);
        assert_pub_crate(&item.vis, struct_name);

        for field in &item.fields {
            let field_name = field
                .ident
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<unnamed>".to_string());
            assert_pub_crate(&field.vis, &format!("{struct_name}.{field_name}"));
        }
    }
}
