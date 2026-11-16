// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native component scenarios; the parent retains the stable test roster.

use super::*;

pub(super) fn native_unit_values_preserve_raw_effects_and_clear_them_at_upstream_consumers() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Prophetic() -> bool { true }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn UnitProphetic() { () }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedSpecUnitCall() { UnitProphetic() }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Lemma(_value: bool) {}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn AcceptedTail() { Lemma(Prophetic()) }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn AcceptedExplicitReturn() { return Lemma(Prophetic()); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn AcceptedBinding() { let _unit = Lemma(Prophetic()); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn AcceptedEffectfulIf() { if Prophetic() { Lemma(false) } else { Lemma(false) } }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn AcceptedPureIf() { #[verifier::prophetic] let condition = true; if condition { () } else { () } }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn GoodDiscard() { Lemma(Prophetic()); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn GoodIfDiscard() { if Prophetic() { Lemma(false) } else { Lemma(false) }; }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedSpecTail(n: u64) {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { #[verifier::proof_in_spec] { Lemma(Prophetic()) } }
    else { AcceptedSpecTail(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn GoodSpecDiscard(n: u64) {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { #[verifier::proof_in_spec] { Lemma(Prophetic()); } }
    else { GoodSpecDiscard(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn GoodSpecAnnotated(n: u64) {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { #[verifier::proof_in_spec] { Lemma(Prophetic()) } }
    else { GoodSpecAnnotated(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn UnitPredicate(_unit: ()) -> bool { true }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn BadProofUnitComparison(n: u64) -> bool {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { ghost_value_builtin_fixture::spec_eq(#[verifier::proof_in_spec] { Lemma(Prophetic()) }, ()) }
    else { BadProofUnitComparison(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedProofUnitComparisonDiscard(n: u64) -> bool {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { ghost_value_builtin_fixture::spec_eq(#[verifier::proof_in_spec] { Lemma(Prophetic()); }, ()) }
    else { AcceptedProofUnitComparisonDiscard(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn BadPureUnitComparison() -> bool {
    let condition = Prophetic();
    ghost_value_builtin_fixture::spec_eq(if condition { () } else { () }, ())
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn BadSpecUnitComparison() -> bool { ghost_value_builtin_fixture::spec_eq(UnitProphetic(), ()) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedProofUnitBinding(n: u64) -> bool {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 {
        let unit = #[verifier::proof_in_spec] { Lemma(Prophetic()) };
        ghost_value_builtin_fixture::spec_eq(unit, ())
    } else { AcceptedProofUnitBinding(n - 1) }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedPureUnitBinding() -> bool {
    let condition = Prophetic();
    let unit = if condition { () } else { () };
    ghost_value_builtin_fixture::spec_eq(unit, ())
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn AcceptedUnitArgument(n: u64) -> bool {
    ghost_value_builtin_fixture::decreases(n);
    if n == 0 { UnitPredicate(#[verifier::proof_in_spec] { Lemma(Prophetic()) }) }
    else { AcceptedUnitArgument(n - 1) }
}
"#,
        |tcx, read| {
            use trust_vc_vcir::wf::{check_crate, WfClass};
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            assert!(
                read.refusals().next().is_none(),
                "{:?}",
                read.refusals().collect::<Vec<_>>()
            );
            let errors = check_crate(&read.krate);
            assert!(
                errors.iter().all(|error| error.class == WfClass::User),
                "{errors:?}"
            );
            for name in [
                "AcceptedSpecTail",
                "GoodSpecDiscard",
                "GoodSpecAnnotated",
                "BadProofUnitComparison",
                "AcceptedProofUnitComparisonDiscard",
                "AcceptedProofUnitBinding",
                "AcceptedUnitArgument",
            ] {
                let owner = named(tcx, name);
                let id = read
                    .fn_defs
                    .iter()
                    .find_map(|(id, actual)| (*actual == owner).then_some(*id))
                    .unwrap();
                assert!(
                    read.krate.rec_group(id).is_some(),
                    "{name} must retain its actual recursive call edge"
                );
            }
            for name in [
                "BadProofUnitComparison",
                "BadPureUnitComparison",
                "BadSpecUnitComparison",
            ] {
                let owner = named(tcx, name);
                let id = read
                    .fn_defs
                    .iter()
                    .find_map(|(id, actual)| (*actual == owner).then_some(*id))
                    .unwrap();
                assert!(
                    errors.iter().any(|error| error.function == Some(id)
                        && error.message.contains("prophetic value not allowed")),
                    "{name}: {errors:?}"
                );
            }
            for name in [
                "Prophetic",
                "UnitProphetic",
                "AcceptedSpecUnitCall",
                "Lemma",
                "AcceptedTail",
                "AcceptedExplicitReturn",
                "AcceptedBinding",
                "AcceptedEffectfulIf",
                "AcceptedPureIf",
                "GoodDiscard",
                "GoodIfDiscard",
                "AcceptedSpecTail",
                "GoodSpecDiscard",
                "GoodSpecAnnotated",
                "UnitPredicate",
                "AcceptedProofUnitBinding",
                "AcceptedPureUnitBinding",
                "AcceptedUnitArgument",
                "AcceptedProofUnitComparisonDiscard",
            ] {
                let owner = named(tcx, name);
                let id = read
                    .fn_defs
                    .iter()
                    .find_map(|(id, actual)| (*actual == owner).then_some(*id))
                    .unwrap();
                assert!(
                    errors.iter().all(|error| error.function != Some(id)),
                    "{name}: {errors:?}"
                );
            }
        },
        false,
    );
    // A measure alone is insufficient. Preserve the actual upstream SST
    // restriction and demonstrate that the positive fixtures above have
    // genuine recursive call-graph edges rather than a waived gate.
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Lemma() {}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn NonRecursive() {
    ghost_value_builtin_fixture::decreases(0u64);
    #[verifier::proof_in_spec] { Lemma(); }
}
"#,
        |tcx, read| {
            let owner = named(tcx, "NonRecursive");
            assert_eq!(read.errors.len(), 1, "{:?}", read.errors);
            assert!(
                read.refusals().next().is_none(),
                "{:?}",
                read.refusals().collect::<Vec<_>>()
            );
            assert!(
                read.errors.iter().any(|error| error.function == Some(owner)
                    && error.phase == crate::messages::Phase::Sst
                    && error.message == crate::messages::termination::PROOF_IN_SPEC_NOT_RECURSIVE),
                "{:?}",
                read.errors
            );
        },
        false,
    );
}
