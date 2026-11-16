// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Formal modes remain declaration data, with strict native layout guards.

use super::*;

#[test]
fn native_field_formals_keep_first_mode_and_original_argument_order() {
    native(
        r#"
#[verus::internal(verus_macro)]
struct Mixed { #[verus::internal(spec)] #[verus::internal(proof)] snapshot: u64, #[verus::internal(proof)] token: u64, live: u64 }
#[verus::internal(verus_macro)]
struct Triple(#[verus::internal(spec)] u64, #[verus::internal(proof)] u64, u64);
#[verus::internal(verus_macro)]
fn Formals(mut value: u64) {
    let record = Mixed { live: { value = 7; value }, snapshot: value, token: value };
    let tuple = Triple(value, value, value);
}
"#,
        |tcx, read| {
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            for name in ["Mixed", "Triple"] {
                let fields = &tcx.adt_def(named(tcx, name)).non_enum_variant().fields;
                let modes: Vec<_> = fields
                    .iter()
                    .map(|field| {
                        crate::reader::datatypes::field_mode(tcx, field, tcx.def_span(field.did))
                            .unwrap()
                    })
                    .collect();
                assert_eq!(modes, [Mode::Spec, Mode::Proof, Mode::Exec], "{name}");
            }
            let owner = named(tcx, "Formals");
            let facts = checked(tcx, "Formals");
            let mut groups = std::collections::HashMap::new();
            for row in facts.availability.arguments() {
                groups.entry(row.call).or_insert_with(Vec::new).push(row);
            }
            assert_eq!(groups.len(), 2);
            for (call, rows) in groups {
                assert_eq!(
                    rows.iter().map(|row| row.position).collect::<Vec<_>>(),
                    [0, 1, 2]
                );
                let hir::Node::Expr(call) = tcx.hir_node(call) else {
                    panic!("actual constructor expression");
                };
                let expected = if matches!(call.kind, hir::ExprKind::Struct(..)) {
                    [Mode::Exec, Mode::Spec, Mode::Proof]
                } else {
                    assert!(matches!(call.kind, hir::ExprKind::Call(..)));
                    [Mode::Spec, Mode::Proof, Mode::Exec]
                };
                assert_eq!(
                    rows.iter().map(|row| row.mode).collect::<Vec<_>>(),
                    expected
                );
                for row in rows {
                    let hir::Node::Expr(original) = tcx.hir_node(row.argument) else {
                        panic!("actual constructor argument");
                    };
                    assert_eq!(
                        facts.availability.argument_for(call, row.position).unwrap(),
                        row
                    );
                    assert_eq!(row.erased, row.mode == Mode::Spec);
                    assert_eq!(original.hir_id.owner.def_id, owner);
                }
            }
            assert!(read
                .item_refusals
                .iter()
                .any(|refusal| refusal.tag == "field-mode"));
            assert!(read.native_ownership.is_empty());
        },
        false,
    );
}

#[test]
fn native_field_modes_preserve_unsupported_attribute_and_reference_gates() {
    native(
        r#"
#[verus::internal(verus_macro)]
struct Unsupported { #[verus::internal(spec)] #[verifier::prophetic] value: u64 }
#[verus::internal(verus_macro)]
struct Holding<'a> { value: &'a mut u64 }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
struct Ghost { value: u64 }
#[verus::internal(verus_macro)] fn ExternalLayout(_value: Holding<'_>) {}
#[verus::internal(verus_macro)] fn BadRead(value: u64) { let _copy = value; }
"#,
        |tcx, read| {
            let unsupported = &tcx
                .adt_def(named(tcx, "Unsupported"))
                .non_enum_variant()
                .fields;
            let unsupported = unsupported
                .iter()
                .find(|field| field.name.as_str() == "value")
                .unwrap();
            let refusal = crate::reader::datatypes::field_mode(
                tcx,
                unsupported,
                tcx.def_span(unsupported.did),
            )
            .unwrap_err();
            assert_eq!(refusal.tag, "attribute");
            assert!(refusal.detail.contains("Prophetic"));
            assert!(read
                .item_refusals
                .iter()
                .any(|refusal| refusal.tag == "attribute" && refusal.detail.contains("Prophetic")));
            assert!(read
                .item_refusals
                .iter()
                .any(|refusal| refusal.tag == "type" && refusal.detail.contains("holds `&mut`")));
            assert!(read
                .item_refusals
                .iter()
                .any(|refusal| refusal.tag == "struct-mode"));
            assert!(!read
                .native_ownership
                .contains(&named(tcx, "ExternalLayout")));
            assert!(read.errors.is_empty(), "{:?}", read.errors);
        },
        false,
    );
}
