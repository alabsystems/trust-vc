// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! AfterBorrow accepts original local-rooted places, not temporary-root fields.

use super::*;

pub(super) fn control() {
    run(
        r#"
#[verus::internal(verus_macro)]
struct Product { live: u64 }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Make(value: u64) -> Product { Product { live: value } }
#[verus::internal(verus_macro)]
fn LocalRoots(reference: &mut u64, value: u64, record: Product) {
    #[verifier::proof_block] {
        let local = availability_builtin_fixture::after_borrow(value);
        let field = availability_builtin_fixture::after_borrow(record.live);
        let deref = availability_builtin_fixture::after_borrow(*reference);
    }
}
#[verus::internal(verus_macro)]
fn TupleTemporary(reference: &mut u64, value: u64) {
    #[verifier::proof_block] {
        let invalid = availability_builtin_fixture::after_borrow((value,).0);
    }
}
#[verus::internal(verus_macro)]
fn StructTemporary(reference: &mut u64, value: u64) {
    #[verifier::proof_block] {
        let invalid = availability_builtin_fixture::after_borrow(Make(value).live);
    }
}
"#,
        |tcx| {
            let context = Context::new(tcx);
            let owner = named(tcx, "LocalRoots");
            let checked = mode_facts(tcx, &context, "LocalRoots");
            let facts = checked.availability.checked(tcx, owner, owner).unwrap();
            for (call, binding, place) in [
                (
                    "availability_builtin_fixture::after_borrow(value)",
                    "value",
                    "value",
                ),
                (
                    "availability_builtin_fixture::after_borrow(record.live)",
                    "record",
                    "record.live",
                ),
                (
                    "availability_builtin_fixture::after_borrow(*reference)",
                    "reference",
                    "*reference",
                ),
            ] {
                let row = argument_usage(tcx, facts, call);
                assert_eq!(row.binding, parameter(tcx, owner, binding));
                assert_eq!(text(tcx, row.place), place);
                assert_eq!(
                    (row.binding_mode, row.place_mode, row.mode),
                    (Mode::Exec, Mode::Exec, Mode::Spec)
                );
                assert!(!row.shadow_check, "{call}");
                assert_eq!(row.erasure, VarErasure::Erase, "{call}");
            }
            for (name, call) in [
                (
                    "TupleTemporary",
                    "availability_builtin_fixture::after_borrow((value,).0)",
                ),
                (
                    "StructTemporary",
                    "availability_builtin_fixture::after_borrow(Make(value).live)",
                ),
            ] {
                match modes::check_with_context(&context, named(tcx, name)) {
                    modes::ModeCheck::Error(error) => {
                        assert!(matches!(error.phase, crate::messages::Phase::Modes));
                        assert_eq!(error.message,
                            "`after_borrow` expects a local variable, possibly with dereferences or field accesses");
                        assert_eq!(tcx.sess.source_map().span_to_snippet(error.span).unwrap(), call);
                    }
                    result => panic!("{name} must reject its temporary root before publishing mode facts: {result:?}"),
                }
            }
            still_closed(tcx, &["LocalRoots", "TupleTemporary", "StructTemporary"]);
        },
    );
}
