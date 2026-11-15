// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reversible negatives over separately captured, genuine native facts.

use super::*;

const ASSOCIATION: &str = "the helper context or actual intrinsic changed";
const PENDING: &str = "pending helpers belong to another native construction or owner";

pub(super) fn reversible(
    scope: &Cohort<'_, '_>,
    pending: &BTreeMap<NativeKey, PendingHelpers>,
    alternate: &Inputs,
    sink: &Sink,
) -> Result<(), String> {
    alternate.revalidate()?;
    if std::ptr::eq(scope.inputs, alternate)
        || alternate.sources.identity() != scope.inputs.sources.identity()
        || alternate.build_origin.is_none()
    {
        return Err("the alternate test Inputs are not a separate real fresh construction".into());
    }
    rejected(
        scope.current(scope.tcx, alternate, scope.metadata),
        ASSOCIATION,
    )?;
    record(
        sink,
        "different_inputs",
        json!({"same_source_recipe": true,
        "distinct_actual_inputs": true, "refusal": ASSOCIATION}),
    )?;

    let (metadata, _) = collect::selections(scope.tcx, scope.inputs, None)?;
    if std::ptr::eq(scope.metadata, &metadata)
        || metadata.crate_ids() != scope.metadata.crate_ids()
        || metadata.digests() != scope.metadata.digests()
    {
        return Err("the recaptured actual metadata does not match the test setup".into());
    }
    rejected(
        scope.current(scope.tcx, scope.inputs, &metadata),
        ASSOCIATION,
    )?;
    record(
        sink,
        "different_metadata_object",
        json!({"equal_actual_native_selections": true,
        "distinct_object": true, "refusal": ASSOCIATION}),
    )?;

    let mut seeds = pending.values();
    let first = seeds
        .next()
        .ok_or("the actual test inventory has no first pending owner")?;
    let second = seeds
        .next()
        .ok_or("the actual test inventory has no second pending owner")?;
    if first.owner == second.owner {
        return Err("the genuine seed owners are not distinct".into());
    }
    cross_scope(scope, first, second, sink)?;
    mixed_owned(scope, first, second, sink)?;
    mutation::changed_bytes(scope, first, sink)?;
    scope.current(scope.tcx, scope.inputs, scope.metadata)?;
    scope.owned.revalidate(scope.inputs, scope.metadata)?;
    record(
        sink,
        "restored_original_scope",
        json!({"full_revalidation": "Passed"}),
    )
}

fn cross_scope(
    scope: &Cohort<'_, '_>,
    first: &PendingHelpers,
    second: &PendingHelpers,
    sink: &Sink,
) -> Result<(), String> {
    let a = genuine::scope(scope)?;
    let b = genuine::scope(scope)?;
    if Arc::ptr_eq(&a.owned, &b.owned) {
        return Err("two actual captures reused one test Arc".into());
    }
    let from_a = genuine::one(&a, first)?;
    rejected(b.finish(from_a), PENDING)?;
    record(
        sink,
        "cross_scope_pending",
        json!({"distinct_actual_arcs": true, "refusal": PENDING}),
    )?;

    let a = genuine::scope(scope)?;
    let b = genuine::scope(scope)?;
    let mut mixed = genuine::one(&a, first)?;
    mixed.extend(genuine::one(&b, second)?);
    if mixed.len() != 2 {
        return Err("the real mixed pending map did not retain two owners".into());
    }
    rejected(a.finish(mixed), PENDING)?;
    record(
        sink,
        "mixed_pending",
        json!({"actual_owners": 2, "refusal": PENDING}),
    )?;

    let a = genuine::scope(scope)?;
    let actual = genuine::pending(&a, first)?;
    rejected(a.finish(BTreeMap::from([(second.owner, actual)])), PENDING)?;
    record(
        sink,
        "wrong_pending_map_owner",
        json!({"actual_different_owner": true, "refusal": PENDING}),
    )
}

fn mixed_owned(
    scope: &Cohort<'_, '_>,
    first: &PendingHelpers,
    second: &PendingHelpers,
    sink: &Sink,
) -> Result<(), String> {
    let a = genuine::scope(scope)?;
    let b = genuine::scope(scope)?;
    if Arc::ptr_eq(&a.owned, &b.owned) {
        return Err("two actual captures reused one test Arc".into());
    }
    let from_a = genuine::one(&a, first)?;
    let from_b = genuine::one(&b, second)?;
    let a = a.finish(from_a)?;
    let b = b.finish(from_b)?;
    if a.len() != 1 || b.len() != 1 {
        return Err("the genuine owned test maps are incomplete".into());
    }
    rejected(
        revalidate_all(scope.inputs, scope.metadata, a.values().chain(b.values())),
        "a Keep helper packet mixes native construction scopes",
    )?;
    record(
        sink,
        "mixed_owned",
        json!({"genuine_individual_finishes": 2,
        "combined_revalidation": "Rejected"}),
    )
}
