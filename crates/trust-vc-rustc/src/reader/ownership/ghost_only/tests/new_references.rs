// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native component scenarios; the parent retains the stable test roster.

use super::*;

pub(super) fn native_new_reference_spec_intrinsics_preserve_opaque_types_and_resolved_definitions()
{
    native_options(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Current(reference: &mut u64) -> u64 { ghost_value_builtin_fixture::mut_ref_current(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Future(reference: &mut u64) -> u64 { ghost_value_builtin_fixture::mut_ref_future(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Final(reference: &mut u64) -> u64 { *ghost_value_builtin_fixture::final_(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Resolved(reference: &mut u64) -> bool { ghost_value_builtin_fixture::has_resolved(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn ResolvedShared(reference: &&mut u64) -> bool { ghost_value_builtin_fixture::has_resolved_unsized(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Identity(reference: &mut u64) -> &mut u64 { reference }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Forward(reference: &mut u64) -> &mut u64 { Identity(reference) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn CurrentThroughIdentity(reference: &mut u64) -> u64 { ghost_value_builtin_fixture::mut_ref_current(Identity(reference)) }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn TupleCurrent(reference: (&mut u64, u64)) -> u64 { ghost_value_builtin_fixture::mut_ref_current(reference.0) }
// The spelling is deliberately identical to the genuine diagnostic member.
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn mut_ref_current(reference: &mut u64) -> u64 { *reference }
"#,
        |tcx, read| {
            use crate::verus_items::VerusItem;
            use trust_vc_vcir::{Body, ExprKind, Ty};
            assert!(read.errors.is_empty(), "{:?}", read.errors);
            assert!(
                read.refusals().next().is_none(),
                "{:?}",
                read.refusals().collect::<Vec<_>>()
            );
            assert!(
                read.verify_refusals.is_empty(),
                "{:?}",
                read.verify_refusals
            );
            let declarations = |name| {
                let owner = named(tcx, name);
                read.krate
                    .fns
                    .iter()
                    .find(|function| read.fn_defs.get(&function.id) == Some(&owner))
                    .unwrap()
            };
            let current = declarations("Current");
            assert_eq!(
                current.locals[current.params[0].index()].ty,
                Ty::MutRef(Box::new(Ty::uint(64)))
            );
            assert!(
                matches!(&current.body, Body::Spec(value) if matches!(&value.kind, ExprKind::MutRefCurrent(_)))
            );
            for name in ["Future", "Final"] {
                let function = declarations(name);
                assert!(function.attrs.prophetic);
                assert!(
                    matches!(&function.body, Body::Spec(value) if matches!(&value.kind, ExprKind::MutRefFuture(_)))
                );
            }
            for name in ["Resolved", "ResolvedShared"] {
                assert!(
                    matches!(&declarations(name).body, Body::Spec(value) if matches!(&value.kind, ExprKind::HasResolved(_)))
                );
            }
            let identity = declarations("Identity");
            assert_eq!(
                identity.locals[identity.ret.index()].ty,
                Ty::MutRef(Box::new(Ty::uint(64)))
            );
            assert!(matches!(&declarations("Forward").body, Body::Spec(value)
                if matches!(&value.kind, ExprKind::Call { callee, .. } if *callee == identity.id)));
            assert!(
                matches!(&declarations("CurrentThroughIdentity").body, Body::Spec(value)
                if matches!(&value.kind, ExprKind::MutRefCurrent(reference)
                    if matches!(&reference.kind, ExprKind::Call { callee, .. } if *callee == identity.id)))
            );
            let table = crate::reader::verus_item_table(tcx);
            assert_eq!(table.get(&named(tcx, "mut_ref_current").to_def_id()), None);
            assert!(table
                .iter()
                .any(|(definition, item)| !definition.is_local()
                    && *item == VerusItem::MutRefCurrent));
            let errors = trust_vc_vcir::wf::check_crate(&read.krate);
            assert!(errors.is_empty(), "{errors:?}");
            assert!(read.native_ownership.is_empty());
            // This diagnostic fixture cannot issue an SDK, import, or native
            // storage/availability capability merely by carrying these names.
        },
        false,
        ReadOptions {
            new_mut_ref: true,
            ..ReadOptions::default()
        },
    );
}

pub(super) fn native_new_reference_exec_storage_and_first_class_final_remain_explicitly_closed() {
    native_options(
        r#"
#[verus::internal(verus_macro)]
fn Exec(reference: &mut u64) { *reference = 3; }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Proof(reference: &mut u64) { let _value = ghost_value_builtin_fixture::mut_ref_current(reference); }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn BareFinal(reference: &mut u64) -> &mut u64 { ghost_value_builtin_fixture::final_(reference) }
"#,
        |tcx, read| {
            for name in ["Exec", "Proof", "BareFinal"] {
                let owner = named(tcx, name);
                let record = read
                    .fns
                    .iter()
                    .find(|record| record.def_id == owner)
                    .unwrap();
                assert!(
                    matches!(&record.status, crate::reader::FnStatus::Refused(refusal) if refusal.tag == "new-mut-ref"),
                    "{name}: {:?}",
                    record.status
                );
            }
            assert!(read.native_ownership.is_empty());
        },
        false,
        ReadOptions {
            new_mut_ref: true,
            ..ReadOptions::default()
        },
    );
}
