// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Original HIR controls for the raw effect check at a native proof wrapper.
//! The diagnostic fixture grants no SDK, import, or ownership authority.

use super::*;

pub(super) fn native_ghost_block_tail_preserves_raw_proof_mode_effects() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Prophetic() -> bool { true }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Implicit(_value: bool) {}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Written(_value: bool) -> () { () }
#[verus::internal(verus_macro)]
fn ExecBad() { #[verifier::proof_block] { Implicit(Prophetic()) } }
#[verus::internal(verus_macro)]
fn ExecSemicolon() { #[verifier::proof_block] { Implicit(Prophetic()); } }
#[verus::internal(verus_macro)]
fn ExecWritten() { #[verifier::proof_block] { Written(Prophetic()) } }
"#,
        |tcx, read| {
            use crate::reader::{attrs, modes};
            use trust_vc_vcir::wf::{check_crate, WfClass};
            use trust_vc_vcir::Mode;

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

            // Check the actual native declaration rule. An implicit proof
            // Unit return has Proof mode; a written Unit return defaults to
            // Spec. The wrapper checks this distinction before Unit clearing.
            for (name, expected) in [("Implicit", Mode::Proof), ("Written", Mode::Spec)] {
                let owner = named(tcx, name);
                let parsed = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)));
                let signature = modes::local_signature_modes(
                    tcx,
                    owner,
                    owner,
                    parsed
                        .mode
                        .expect("the actual declaration carries its mode"),
                    &parsed,
                    false,
                    tcx.def_span(owner),
                )
                .unwrap();
                assert_eq!(signature.ret.mode, expected, "{name}");
            }

            let errors = check_crate(&read.krate);
            let function = |name| {
                let owner = named(tcx, name);
                read.fn_defs
                    .iter()
                    .find_map(|(id, actual)| (*actual == owner).then_some(*id))
                    .unwrap()
            };
            // Establish the genuine acceptance controls before the expected
            // rejection, so a red run cannot hide a blanket refusal.
            for name in [
                "Prophetic",
                "Implicit",
                "Written",
                "ExecSemicolon",
                "ExecWritten",
            ] {
                assert!(
                    errors
                        .iter()
                        .all(|error| error.function != Some(function(name))),
                    "{name}: {errors:?}"
                );
            }
            let bad = function("ExecBad");
            assert!(
                errors.iter().any(|error| error.class == WfClass::User
                    && error.function == Some(bad)
                    && error.message.contains("prophetic")),
                "the raw Proof tail must be rejected before Unit clearing: {errors:?}"
            );
            assert!(
                errors
                    .iter()
                    .all(|error| error.class == WfClass::User && error.function == Some(bad)),
                "{errors:?}"
            );
        },
        false,
    );
}

pub(super) fn native_ghost_block_wrappers_branches_and_instances_retain_checked_modes() {
    native(
        r#"
#[verus::internal(verus_macro)] #[verus::internal(spec)] #[verifier::prophetic]
fn Prophetic() -> bool { true }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Implicit(_value: bool) {}
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn Written(_value: bool) -> () { () }
#[verus::internal(verus_macro)]
fn WrappedBad() { #[verifier::proof_block] { { Implicit(Prophetic()) } } }
#[verus::internal(verus_macro)]
fn BranchBad() { #[verifier::proof_block] { if Prophetic() { Implicit(false) } else { Implicit(false) } } }
#[verus::internal(verus_macro)]
fn BranchSemicolon() { #[verifier::proof_block] { if Prophetic() { Implicit(false) } else { Implicit(false) }; } }
#[verus::internal(verus_macro)]
fn MixedSpecBranch() { #[verifier::proof_block] { if Prophetic() { Implicit(false) } else { Written(false) } } }
#[verus::internal(verus_macro)]
fn WrappedWritten() { #[verifier::proof_block] { { Written(Prophetic()) } } }
#[verus::internal(verus_macro)]
fn Empty() { #[verifier::proof_block] {} }
#[verus::internal(verus_macro)]
fn NestedNoTail() { #[verifier::proof_block] { { Implicit(false); } } }
#[verus::internal(verus_macro)]
fn UnitField() { #[verifier::proof_block] { ((),).0 } }
#[verus::internal(verus_macro)]
fn AuthoredUnitField() { #[verifier::proof_block] { let tuple = (Implicit(Prophetic()),); tuple.0 } }
#[verus::internal(verus_macro)]
fn TemporaryUnitField() { #[verifier::proof_block] { (Implicit(Prophetic()),).0 } }
#[verus::internal(verus_macro)]
fn GenericBad<T>(_value: T) { #[verifier::proof_block] { Implicit(Prophetic()) } }
#[verus::internal(verus_macro)]
fn GenericWritten<T>(_value: T) { #[verifier::proof_block] { Written(Prophetic()) } }
#[verus::internal(verus_macro)]
fn Instantiate() { GenericBad(3u64); GenericWritten(false); }
"#,
        |tcx, read| {
            use trust_vc_vcir::wf::{
                function_prophecy_diagnostics, ghost_tail_modes, GhostTailModeClass,
            };
            use trust_vc_vcir::{Body, FnRole, StmtKind, Ty, WfClass};
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
            let implicit = named(tcx, "Implicit");
            let written = named(tcx, "Written");
            let original = &read.ghost_ownership[&implicit];
            assert!(original.permits_implicit_unit_return(tcx, implicit));
            assert!(!original.permits_implicit_unit_return(tcx, written));
            assert!(!read.ghost_ownership[&written].permits_implicit_unit_return(tcx, written));
            let function = |name| {
                let owner = named(tcx, name);
                read.fn_defs
                    .iter()
                    .find_map(|(id, actual)| (*actual == owner).then_some(*id))
                    .unwrap()
            };
            let rejected = [
                function("WrappedBad"),
                function("BranchBad"),
                function("GenericBad"),
            ];
            let mut accepted = [
                "Prophetic",
                "Implicit",
                "Written",
                "BranchSemicolon",
                "MixedSpecBranch",
                "WrappedWritten",
                "Empty",
                "NestedNoTail",
                "UnitField",
                "AuthoredUnitField",
                "TemporaryUnitField",
                "GenericWritten",
                "Instantiate",
            ]
            .into_iter()
            .map(function)
            .collect::<Vec<_>>();
            let raw_modes = ghost_tail_modes(&read.krate);
            let check_generic_body = |id, expected_class, prophetic| {
                let declaration = read
                    .krate
                    .fn_decl(id)
                    .expect("the actual native declaration exists");
                let Body::Stmts(block) = &declaration.body else {
                    panic!("the actual generic source or instance lost its body: {id:?}");
                };
                let physical_tails = block
                    .stmts
                    .iter()
                    .filter_map(|statement| {
                        matches!(&statement.kind, StmtKind::GhostTail { .. })
                            .then_some(statement.span)
                    })
                    .collect::<Vec<_>>();
                let observed = raw_modes
                    .iter()
                    .filter(|row| row.function == id)
                    .collect::<Vec<_>>();
                assert_eq!(physical_tails.len(), 1, "{id:?}");
                assert_eq!(observed.len(), 1, "{id:?}: {observed:?}");
                assert_eq!(observed[0].span, physical_tails[0], "{id:?}");
                assert_eq!(observed[0].class, Some(expected_class), "{id:?}");
                let diagnostics = function_prophecy_diagnostics(&read.krate, id)
                    .expect("the diagnostic selects the same actual declaration");
                if prophetic {
                    assert_eq!(diagnostics.len(), 1, "{id:?}: {diagnostics:?}");
                    assert!(
                        diagnostics.iter().all(|error| error.class == WfClass::User
                            && error.function == Some(id)
                            && error.message.contains("'Ghost' wrapper")),
                        "{id:?}: {diagnostics:?}"
                    );
                } else {
                    assert!(diagnostics.is_empty(), "{id:?}: {diagnostics:?}");
                }
            };
            for (name, expected_class, prophetic) in [
                ("GenericWritten", GhostTailModeClass::Spec, false),
                ("GenericBad", GhostTailModeClass::NonSpec, true),
            ] {
                let id = function(name);
                assert_eq!(read.krate.fn_decl(id).unwrap().role, FnRole::Item);
                check_generic_body(id, expected_class, prophetic);
            }
            let mut instances = 0;
            let mut bad_instances = Vec::new();
            let mut written_instances = Vec::new();
            for declaration in &read.krate.fns {
                if declaration.role != FnRole::Instance {
                    continue;
                }
                let source = declaration
                    .attrs
                    .instance
                    .as_ref()
                    .expect("a real instance retains its original declaration");
                assert_ne!(declaration.id, source.declaration);
                if source.declaration == function("GenericBad") {
                    assert_eq!(source.type_args, vec![Ty::uint(64)]);
                    bad_instances.push(declaration.id);
                    check_generic_body(declaration.id, GhostTailModeClass::NonSpec, true);
                } else {
                    assert_eq!(source.declaration, function("GenericWritten"));
                    assert_eq!(source.type_args, vec![Ty::Bool]);
                    written_instances.push(declaration.id);
                    check_generic_body(declaration.id, GhostTailModeClass::Spec, false);
                    accepted.push(declaration.id);
                }
                instances += 1;
            }
            assert_eq!(
                instances, 2,
                "both concrete native generic bodies must be read"
            );
            assert_eq!(bad_instances.len(), 1, "{bad_instances:?}");
            assert_eq!(written_instances.len(), 1, "{written_instances:?}");
            assert_ne!(bad_instances[0], written_instances[0]);
            let errors = trust_vc_vcir::check_crate(&read.krate);
            // Public diagnostics belong to the source declaration. The
            // actual instance effects were checked above before attribution.
            assert_eq!(errors.len(), rejected.len(), "{errors:?}");
            for id in accepted {
                assert!(
                    errors.iter().all(|error| error.function != Some(id)),
                    "{id:?}: {errors:?}"
                );
            }
            for id in &rejected {
                assert!(
                    errors.iter().any(|error| error.class == WfClass::User
                        && error.function == Some(*id)
                        && error.message.contains("prophetic")),
                    "{id:?}: {errors:?}"
                );
            }
            assert!(
                errors.iter().all(|error| error.class == WfClass::User
                    && error.function.is_some_and(|id| rejected.contains(&id))),
                "{errors:?}"
            );
        },
        false,
    );
}
