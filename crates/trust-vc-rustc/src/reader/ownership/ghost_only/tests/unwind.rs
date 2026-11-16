// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual native unwind contracts, without SDK or import capabilities.

use super::*;
use trust_vc_vcir::{Body, ExprKind, FnRole, UnwindSpec};

mod diagnostic_source;
mod diagnostics;
mod drops;
mod native;
mod traits;

fn function<'a>(tcx: TyCtxt<'_>, read: &'a CrateRead, name: &str) -> &'a trust_vc_vcir::FnDecl {
    let owner = named(tcx, name);
    let id = read
        .fn_defs
        .iter()
        .find_map(|(id, actual)| (*actual == owner).then_some(*id))
        .unwrap();
    read.krate.fn_decl(id).unwrap()
}

fn clean(read: &CrateRead) {
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
    assert!(
        read.pending_item_refusals.is_empty(),
        "{:?}",
        read.pending_item_refusals
    );
    assert!(
        trust_vc_vcir::check_crate(&read.krate).is_empty(),
        "{:?}",
        trust_vc_vcir::check_crate(&read.krate)
    );
}

#[test]
fn native_unwind_headers_calls_and_instances_preserve_contracts() {
    native::run(
        r#"
#[verus::internal(verus_macro)]
fn May() {}
#[verus::internal(verus_macro)]
fn No() { unwind_builtin_fixture::no_unwind(); }
#[verus::internal(verus_macro)]
fn Conditional(flag: bool) { unwind_builtin_fixture::no_unwind_when(flag); }
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Prophetic() -> bool { true }
#[verus::internal(verus_macro)]
fn PropheticCondition() { unwind_builtin_fixture::no_unwind_when(Prophetic()); }
#[verus::internal(verus_macro)]
fn Calls(flag: bool) { unwind_builtin_fixture::no_unwind_when(flag); Conditional(flag); No(); }
#[verus::internal(verus_macro)]
fn Generic<T>(_value: T, enabled: bool) { unwind_builtin_fixture::no_unwind_when(enabled); }
#[verus::internal(verus_macro)]
fn Instantiate() { Generic(3u64, true); }
"#,
        |tcx, read| {
            clean(read);
            assert!(function(tcx, read, "May").unwind.is_none());
            assert!(matches!(
                function(tcx, read, "May").unwind_spec(),
                UnwindSpec::MayUnwind
            ));
            assert!(matches!(
                function(tcx, read, "No").unwind,
                Some(UnwindSpec::NoUnwind)
            ));
            assert!(matches!(
                function(tcx, read, "PropheticCondition").unwind,
                Some(UnwindSpec::NoUnwindWhen(_))
            ));
            for name in ["Conditional", "Calls", "Generic"] {
                let declaration = function(tcx, read, name);
                let condition = declaration.unwind.as_ref().unwrap().condition().unwrap();
                let ExprKind::Read(place) = &condition.kind else {
                    panic!("the actual Boolean parameter must be retained");
                };
                assert_eq!(place.local, *declaration.params.last().unwrap());
                assert!(place.projections.is_empty());
                assert_eq!(condition.ty, trust_vc_vcir::Ty::Bool);
            }
            let generic = function(tcx, read, "Generic");
            assert_eq!(generic.role, FnRole::Item);
            assert_eq!(
                generic.type_params.len(),
                1,
                "the original remains unconstrained and generic"
            );
            let instances = read
                .krate
                .fns
                .iter()
                .filter(|decl| {
                    decl.role == FnRole::Instance
                        && decl
                            .attrs
                            .instance
                            .as_ref()
                            .is_some_and(|origin| origin.declaration == generic.id)
                })
                .collect::<Vec<_>>();
            assert_eq!(instances.len(), 1);
            let instance = instances[0];
            assert_eq!(instance.role, FnRole::Instance);
            assert_ne!(instance.id, generic.id);
            assert_eq!(
                instance.attrs.instance.as_ref().unwrap().type_args,
                vec![trust_vc_vcir::Ty::uint(64)]
            );
            assert!(matches!(instance.body, Body::Stmts(_)));
            let condition = instance.unwind.as_ref().unwrap().condition().unwrap();
            assert!(
                matches!(&condition.kind, ExprKind::Read(place) if place.local == instance.params[1])
            );
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            // Implicit Drop has Verus's documented no-unwind assumption.
            // The original generic body is checked; an instance is attributed
            // to that original rather than silently standing in for it.
            assert!(
                matches!(
                    generated.get(generic.id),
                    Some(trust_vc_vcir::vcgen::FnVcs::Checks(_))
                ),
                "{generated:?}"
            );
            assert!(
                matches!(
                    generated.get(instance.id),
                    Some(trust_vc_vcir::vcgen::FnVcs::Instance)
                ),
                "{generated:?}"
            );
            let calls = generated
                .fns
                .iter()
                .find(|(id, _)| *id == function(tcx, read, "Calls").id)
                .unwrap();
            let trust_vc_vcir::vcgen::FnVcs::Checks(checks) = &calls.1 else {
                panic!("the local caller must reach real VC generation: {calls:?}");
            };
            assert!(checks.iter().any(|check| matches!(check.kind,
            trust_vc_vcir::vcgen::CheckKind::Unwind { callee, .. } if callee == function(tcx, read, "Conditional").id)));
        },
    );
}

#[test]
fn native_unwind_rejects_duplicate_and_nonexec_headers_without_opening_masks() {
    native::run(
        r#"
#[verus::internal(verus_macro)]
fn No() { unwind_builtin_fixture::no_unwind(); }
#[verus::internal(verus_macro)]
fn Duplicate() { unwind_builtin_fixture::no_unwind(); unwind_builtin_fixture::no_unwind_when(true); }
#[verus::internal(verus_macro)]
fn Reverse() { unwind_builtin_fixture::no_unwind_when(true); unwind_builtin_fixture::no_unwind(); }
#[verus::internal(verus_macro)]
fn ConditionalTwice() { unwind_builtin_fixture::no_unwind_when(true); unwind_builtin_fixture::no_unwind_when(false); }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn ProofHeader() { unwind_builtin_fixture::no_unwind(); }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn SpecHeader() { unwind_builtin_fixture::no_unwind_when(true); }
#[verus::internal(verus_macro)]
fn Impure(mut flag: bool) { unwind_builtin_fixture::no_unwind_when({ flag = true; flag }); }
#[verus::internal(verus_macro)]
fn Mask() { unwind_builtin_fixture::opens_invariants_none(); No(); }
#[verus::internal(verus_macro)] #[verus::internal(spec)]
fn Hidden() -> bool { true }
#[verus::internal(verus_macro)]
pub fn PublicHeader() { unwind_builtin_fixture::no_unwind_when(Hidden()); }
"#,
        |tcx, read| {
            for name in ["Duplicate", "Reverse", "ConditionalTwice"] {
                let owner = named(tcx, name);
                assert!(
                    read.errors.iter().any(|error| error.function == Some(owner)
                        && error.phase == crate::messages::Phase::RustToVir
                        && error.message == crate::messages::header::SECOND_UNWIND),
                    "{name}: {:?}",
                    read.errors
                );
            }
            for name in ["ProofHeader", "SpecHeader"] {
                let owner = named(tcx, name);
                assert!(
                    read.errors.iter().any(|error| error.function == Some(owner)
                        && error.message
                            == "an 'unwind' specification can only be given on exec functions"),
                    "{name}: {:?}",
                    read.errors
                );
            }
            assert!(
                read.errors
                    .iter()
                    .any(|error| error.function == Some(named(tcx, "Impure"))
                        && error.message == crate::messages::modes::ASSIGN_IN_PURE),
                "{:?}",
                read.errors
            );
            assert!(
                read.errors
                    .iter()
                    .any(|error| error.function == Some(named(tcx, "PublicHeader"))
                        && error.message
                            == crate::messages::wf::private_reference(
                                "unwind clause of public function",
                                "function"
                            )),
                "{:?}",
                read.errors
            );
            let mask = read
                .fns
                .iter()
                .find(|record| record.def_id == named(tcx, "Mask"))
                .unwrap();
            assert!(
                matches!(&mask.status, crate::reader::FnStatus::Refused(refusal)
            if refusal.tag == "header" && refusal.detail.contains("opens_invariants none")),
                "{:?}",
                mask.status
            );
        },
    );
}
