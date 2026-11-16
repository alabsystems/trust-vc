// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Explicit prophecy nodes suppress shadow marking only in their own operands.

use super::*;

pub(super) fn control() {
    run(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Before(value: u64) -> u64 { value }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn After(value: u64) -> u64 { value }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Identity(reference: &mut u64) -> &mut u64 { reference }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Forward(reference: &mut u64) -> &mut u64 { Identity(reference) }
#[verus::internal(verus_macro)]
fn Suppression(reference: &mut u64, value: u64) {
    #[verifier::proof_block] {
        let before = Before(value);
        let old = availability_builtin_fixture::old(reference);
        let resolved = availability_builtin_fixture::has_resolved(value);
        let after_borrow = availability_builtin_fixture::after_borrow(value);
        let future = availability_builtin_fixture::mut_ref_future(reference);
        let final_reference = availability_builtin_fixture::final_(reference);
        let current = availability_builtin_fixture::mut_ref_current(reference);
        let after = After(value);
    }
}
"#,
        |tcx| {
            let context = Context::new(tcx);
            let owner = named(tcx, "Suppression");
            let checked = mode_facts(tcx, &context, "Suppression");
            let facts = checked.availability.checked(tcx, owner, owner).unwrap();
            for call in [
                "Before(value)",
                "After(value)",
                "availability_builtin_fixture::mut_ref_future(reference)",
                "availability_builtin_fixture::final_(reference)",
                "availability_builtin_fixture::mut_ref_current(reference)",
            ] {
                let row = argument_usage(tcx, facts, call);
                assert!(row.shadow_check, "{call}");
                assert_eq!(
                    (row.binding_mode, row.mode, row.erasure),
                    (Mode::Exec, Mode::Spec, VarErasure::Shadow),
                    "{call}"
                );
            }
            for call in [
                "availability_builtin_fixture::old(reference)",
                "availability_builtin_fixture::has_resolved(value)",
                "availability_builtin_fixture::after_borrow(value)",
            ] {
                let row = argument_usage(tcx, facts, call);
                assert!(!row.shadow_check, "{call}");
                assert_eq!(
                    (row.binding_mode, row.mode, row.erasure),
                    (Mode::Exec, Mode::Spec, VarErasure::Erase),
                    "{call}"
                );
            }
            let forwarded = mode_facts(tcx, &context, "Forward");
            let forward_owner = named(tcx, "Forward");
            let forward = forwarded
                .availability
                .checked(tcx, forward_owner, forward_owner)
                .unwrap();
            assert!(forward.adjustments().iter().any(|row| row.kinds
                == vec![
                    AdjustmentKind::BuiltinDeref,
                    AdjustmentKind::MutableBorrow,
                    AdjustmentKind::SpecReborrow
                ]));
            assert!(forward
                .uses()
                .iter()
                .all(|row| row.binding_mode == Mode::Spec
                    && row.mode == Mode::Spec
                    && row.shadow_check
                    && row.erasure == VarErasure::Erase));
            assert!(!forward.uses().is_empty());
            still_closed(tcx, &["Suppression"]);
        },
    );
}
