// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A diagnostic item cannot substitute for a live owned import.

use super::*;

#[test]
fn native_sequence_length_diagnostic_item_has_no_import_authority() {
    native(
        r#"
#[rustc_diagnostic_item = "verus::vstd::seq::Seq::len"]
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Counterfeit(value: u64) -> u64 { value }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Client(value: u64) -> u64 { Counterfeit(value) }
"#,
        |tcx, read| {
            let definition = named(tcx, "Counterfeit");
            assert_eq!(
                crate::reader::verus_item_table(tcx).get(&definition.to_def_id()),
                Some(&crate::verus_items::VerusItem::SeqLen)
            );
            let client = read
                .fns
                .iter()
                .find(|record| record.def_id == named(tcx, "Client"))
                .unwrap();
            assert!(
                matches!(&client.status, crate::reader::FnStatus::Refused(refusal) if refusal.tag == "owned-seq-len"),
                "{:?}",
                client.status
            );
            assert!(read
                .krate
                .fns
                .iter()
                .all(|function| function.role != trust_vc_vcir::FnRole::Imported));
            assert!(read.native_ownership.is_empty());
        },
        false,
    );
}

#[test]
fn native_sequence_index_diagnostic_item_has_no_source_family_authority() {
    native(
        r#"
#[rustc_diagnostic_item = "verus::vstd::seq::Seq::index"]
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Counterfeit(value: u64, index: u64) -> u64 { value }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Client(value: u64) -> u64 { Counterfeit(value, 0) }
"#,
        |tcx, read| {
            let definition = named(tcx, "Counterfeit");
            assert_eq!(
                crate::reader::verus_item_table(tcx).get(&definition.to_def_id()),
                Some(&crate::verus_items::VerusItem::SeqIndex)
            );
            let client = read
                .fns
                .iter()
                .find(|record| record.def_id == named(tcx, "Client"))
                .unwrap();
            assert!(
                matches!(&client.status, crate::reader::FnStatus::Refused(refusal) if refusal.tag == "owned-seq-index"),
                "{:?}",
                client.status
            );
            assert!(read
                .krate
                .fns
                .iter()
                .all(|function| function.role != trust_vc_vcir::FnRole::Imported));
            assert!(read.native_ownership.is_empty());
        },
        false,
    );
}
