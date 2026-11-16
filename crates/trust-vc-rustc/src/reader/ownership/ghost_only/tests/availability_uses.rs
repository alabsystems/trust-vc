// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual HIR mode observations. These do not perform a shadow borrow check
//! and do not admit native executable/proof references or closures.

use super::*;
use crate::reader::modes::{
    self, AccessKind, AdjustmentKind, AvailabilityFacts, PlaceUse, VarErasure,
};

mod after_borrow_places;
mod lookups;
mod native;
mod suppression;
use native::{parameter, run, text, Context};

pub(super) fn after_borrow_place_grammar() {
    after_borrow_places::control();
}

fn mode_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &Context<'tcx>,
    name: &str,
) -> modes::CheckedModes<'tcx> {
    match modes::check_with_context(context, named(tcx, name)) {
        modes::ModeCheck::Clean(facts) => facts,
        result => panic!("the actual native mode walk for {name} must complete: {result:?}"),
    }
}

fn usage<'a>(
    tcx: TyCtxt<'_>,
    facts: &'a AvailabilityFacts<'_>,
    source: &str,
    access: AccessKind,
) -> &'a PlaceUse {
    let found = facts
        .uses()
        .iter()
        .filter(|row| row.access == access && text(tcx, row.place) == source)
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "{source}: {found:?}");
    found[0]
}

fn argument_usage<'a>(
    tcx: TyCtxt<'_>,
    facts: &'a AvailabilityFacts<'_>,
    call: &str,
) -> &'a PlaceUse {
    let arguments = facts
        .arguments()
        .iter()
        .filter(|row| text(tcx, row.call) == call)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 1, "{call}: {arguments:?}");
    assert_eq!(
        (
            arguments[0].position,
            arguments[0].mode,
            arguments[0].erased
        ),
        (0, Mode::Spec, true)
    );
    let found = facts
        .uses()
        .iter()
        .filter(|row| row.place == arguments[0].argument && row.access == AccessKind::Read)
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "{call}: {found:?}");
    found[0]
}

fn still_closed(tcx: TyCtxt<'_>, names: &[&str]) {
    let read = read_crate(
        tcx,
        ReadOptions {
            new_mut_ref: true,
            ..ReadOptions::default()
        },
    );
    for name in names {
        let owner = named(tcx, name);
        let record = read
            .fns
            .iter()
            .find(|record| record.def_id == owner)
            .unwrap();
        assert!(
            matches!(&record.status, crate::reader::FnStatus::Refused(refusal)
            if refusal.tag == "new-mut-ref"),
            "{name}: {:?}",
            record.status
        );
        assert!(!read.native_ownership.contains(&owner));
        assert!(!read.ghost_ownership.contains_key(&owner));
    }
}

pub(super) fn accesses_and_argument_erasure() {
    run(
        r#"
#[verus::internal(verus_macro)]
struct Product { live: u64, #[verus::internal(spec)] ghost: u64 }
#[verus::internal(verus_macro)]
fn Sink(_live: u64, #[verus::internal(spec)] _ghost: u64) {}
#[verus::internal(verus_macro)]
fn Shared(_reference: &u64) {}
#[verus::internal(verus_macro)]
fn Places(reference: &mut u64, mut record: Product, value: u64, _unused: u64) {
    let copied = record.live;
    record.live = value;
    #[verifier::proof_block] {
        let observed = record.ghost;
        record.ghost = value;
    }
    let borrowed = &mut record.live;
    *borrowed = copied;
    *reference = value;
    Shared(reference);
    Sink(value, value);
    let made = Product { ghost: value, live: copied };
}
#[verus::internal(verus_macro)]
fn Other() {}
"#,
        |tcx| {
            let context = Context::new(tcx);
            let owner = named(tcx, "Places");
            let checked = mode_facts(tcx, &context, "Places");
            let facts = checked.availability.checked(tcx, owner, owner).unwrap();
            let record = parameter(tcx, owner, "record");
            let live = usage(tcx, facts, "record.live", AccessKind::Read);
            assert_eq!(
                (live.binding, live.binding_mode, live.place_mode, live.mode),
                (record, Mode::Exec, Mode::Exec, Mode::Exec)
            );
            assert!(live.shadow_check);
            assert_eq!(live.erasure, VarErasure::Keep);
            let ghost = usage(tcx, facts, "record.ghost", AccessKind::Read);
            assert_eq!(
                (
                    ghost.binding,
                    ghost.binding_mode,
                    ghost.place_mode,
                    ghost.mode
                ),
                (record, Mode::Exec, Mode::Spec, Mode::Spec)
            );
            assert!(ghost.shadow_check);
            assert_eq!(ghost.erasure, VarErasure::Shadow);
            let assign = usage(tcx, facts, "record.ghost", AccessKind::Assign);
            assert_eq!(
                (
                    assign.binding,
                    assign.binding_mode,
                    assign.place_mode,
                    assign.mode
                ),
                (record, Mode::Exec, Mode::Spec, Mode::Spec)
            );
            assert_eq!(
                assign.erasure,
                VarErasure::Keep,
                "a mutable place retains its original root"
            );
            assert!(facts
                .operations()
                .iter()
                .any(|row| row.kind == AccessKind::Assign
                    && row.place == assign.place
                    && text(tcx, row.expression) == "record.ghost = value"
                    && row.place_mode == Mode::Spec
                    && row.mode == Mode::Spec));
            let borrow = usage(tcx, facts, "record.live", AccessKind::MutBorrow);
            assert_eq!(
                (borrow.binding, borrow.place_mode, borrow.mode),
                (record, Mode::Exec, Mode::Exec)
            );
            assert_eq!(borrow.erasure, VarErasure::Keep);
            assert!(facts
                .operations()
                .iter()
                .any(|row| row.kind == AccessKind::MutBorrow
                    && row.place == borrow.place
                    && text(tcx, row.expression) == "&mut record.live"
                    && row.place_mode == Mode::Exec
                    && row.mode == Mode::Exec));
            let sink = facts
                .arguments()
                .iter()
                .filter(|row| text(tcx, row.call) == "Sink(value, value)")
                .collect::<Vec<_>>();
            assert_eq!(sink.len(), 2);
            assert_eq!(
                (sink[0].position, sink[0].mode, sink[0].erased),
                (0, Mode::Exec, false)
            );
            assert_eq!(
                (sink[1].position, sink[1].mode, sink[1].erased),
                (1, Mode::Spec, true)
            );
            let constructor = facts
                .arguments()
                .iter()
                .filter(|row| text(tcx, row.call) == "Product { ghost: value, live: copied }")
                .collect::<Vec<_>>();
            assert_eq!(constructor.len(), 2);
            assert_eq!(
                (
                    constructor[0].position,
                    constructor[0].mode,
                    constructor[0].erased
                ),
                (0, Mode::Spec, true)
            );
            assert_eq!(
                (
                    constructor[1].position,
                    constructor[1].mode,
                    constructor[1].erased
                ),
                (1, Mode::Exec, false)
            );
            assert!(facts
                .adjustments()
                .iter()
                .any(|row| text(tcx, row.expression) == "reference"
                    && row.kinds
                        == vec![AdjustmentKind::BuiltinDeref, AdjustmentKind::SharedBorrow]));
            let unused = parameter(tcx, owner, "_unused");
            assert!(facts.uses().iter().all(|row| row.binding != unused));
            let other = named(tcx, "Other");
            assert!(checked.availability.checked(tcx, other, owner).is_err());
            assert!(checked.availability.checked(tcx, owner, other).is_err());
            for (index, row) in facts.uses().iter().enumerate() {
                assert!(
                    facts.uses()[..index]
                        .iter()
                        .all(|prior| prior.place != row.place || prior.access != row.access),
                    "one physical native access cannot publish duplicate or conflicting modes"
                );
                let hir::Node::Expr(local) = tcx.hir_node(row.local_use) else {
                    panic!("actual local expression");
                };
                let hir::ExprKind::Path(ref path) = local.kind else {
                    panic!("actual local path");
                };
                assert_eq!(
                    tcx.typeck(owner).qpath_res(path, local.hir_id),
                    rustc_hir::def::Res::Local(row.binding)
                );
            }
            lookups::check(tcx, facts);
            still_closed(tcx, &["Places"]);
        },
    );
}

pub(super) fn explicit_prophecy_suppression() {
    suppression::control();
}

pub(super) fn proof_borrow_and_rejected_contexts() {
    run(
        r#"
#[verus::internal(verus_macro)]
fn ProofBorrow(reference: &mut u64) {
    #[verifier::proof_block] { let borrowed = &mut *reference; }
}
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn SpecBorrow(reference: &mut u64) -> &mut u64 {
    let seen = reference;
    &mut *seen
}
#[verus::internal(verus_macro)]
fn OldBorrow(reference: &mut u64) {
    #[verifier::proof_block] { let prior = availability_builtin_fixture::old(&mut *reference); }
}
#[verus::internal(verus_macro)]
fn Closure(reference: &mut u64) { let closure = || *reference; let answer = closure(); }
#[verus::internal(verus_macro)]
fn Other() {}
"#,
        |tcx| {
            let context = Context::new(tcx);
            let owner = named(tcx, "ProofBorrow");
            let checked = mode_facts(tcx, &context, "ProofBorrow");
            let facts = checked.availability.checked(tcx, owner, owner).unwrap();
            let row = usage(tcx, facts, "*reference", AccessKind::MutBorrow);
            assert_eq!(
                (row.binding, row.binding_mode, row.place_mode, row.mode),
                (
                    parameter(tcx, owner, "reference"),
                    Mode::Exec,
                    Mode::Exec,
                    Mode::Exec
                )
            );
            assert!(row.shadow_check);
            assert_eq!(row.erasure, VarErasure::Keep);
            let operations = facts
                .operations()
                .iter()
                .filter(|operation| operation.kind == AccessKind::MutBorrow)
                .collect::<Vec<_>>();
            assert_eq!(operations.len(), 1);
            assert_eq!(
                (
                    operations[0].place,
                    operations[0].place_mode,
                    operations[0].mode
                ),
                (row.place, Mode::Exec, Mode::Proof)
            );
            assert_eq!(text(tcx, operations[0].expression), "&mut *reference");
            let body = tcx.hir_body_owned_by(owner);
            let copied = *body;
            assert_eq!(body.id(), copied.id());
            assert!(original_body(tcx, owner, body));
            assert!(
                !original_body(tcx, owner, &copied),
                "IDs cannot stand in for the original allocation"
            );
            let other = named(tcx, "Other");
            assert!(checked.availability.checked(tcx, other, other).is_err());
            for name in ["SpecBorrow", "OldBorrow"] {
                match modes::check_with_context(&context, named(tcx, name)) {
                    modes::ModeCheck::Error(error) => {
                        assert!(matches!(error.phase, crate::messages::Phase::Modes));
                        assert_eq!(
                            error.message,
                            "mutable borrow is not allowed in spec context"
                        );
                    }
                    result => panic!(
                        "{name} must reject before publishing partial mode facts: {result:?}"
                    ),
                }
            }
            assert!(
                matches!(
                    modes::check_with_context(&context, named(tcx, "Closure")),
                    modes::ModeCheck::Unknown(_)
                ),
                "an unsupported closure must not issue completed facts"
            );
            still_closed(tcx, &["ProofBorrow", "OldBorrow", "Closure"]);
        },
    );
}
