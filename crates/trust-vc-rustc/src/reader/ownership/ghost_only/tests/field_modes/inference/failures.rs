// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unsupported inference never supplies a default mode or ownership receipt.

use super::*;

#[test]
fn native_inference_refuses_missing_foreign_or_owned_mode_authority() {
    native(
        r#"
#[verus::internal(verus_macro)]
fn Assigned(value: u64) { #[verus::internal(infer_mode)] let inferred; inferred = value; }
#[verus::internal(verus_macro)]
fn Missing() { #[verus::internal(infer_mode)] let inferred: u64; }
#[verus::internal(verus_macro)]
fn Initialized(value: u64) { #[verus::internal(infer_mode)] let inferred = value; }
#[verus::internal(verus_macro)]
fn Literal() { #[verus::internal(infer_mode)] let inferred: u64; inferred = 7; }
#[verus::internal(verus_macro)] #[verus::internal(proof)]
fn ProofOnly(#[verus::internal(proof)] value: bool) { #[verus::internal(infer_mode)] let inferred; inferred = value; }
#[verus::internal(verus_macro)]
fn SpecEscape(#[verus::internal(spec)] value: u64) -> u64 {
    #[verus::internal(infer_mode)] let inferred;
    #[verifier::proof_block] { inferred = value; }
    inferred
}
#[verus::internal(verus_macro)]
fn Incompatible(flag: bool, live: u64, #[verus::internal(spec)] ghost: u64) {
    #[verus::internal(infer_mode)] let inferred;
    if flag { inferred = live; } else { #[verifier::proof_block] { inferred = ghost; } }
}
"#,
        |tcx, read| {
            let assigned = named(tcx, "Assigned");
            let body = tcx.hir_body_owned_by(assigned);
            let facts = checked(tcx, "Assigned");
            let original = binding(tcx, assigned, "inferred");
            assert_eq!(
                facts
                    .bindings
                    .mode_for(tcx, assigned, assigned, body, original)
                    .unwrap(),
                Mode::Exec
            );
            let copied = *original;
            assert!(facts
                .bindings
                .mode_for(tcx, assigned, assigned, body, &copied)
                .is_err());
            let copied_body = *body;
            assert!(facts
                .bindings
                .mode_for(tcx, assigned, assigned, &copied_body, original)
                .is_err());
            let missing = named(tcx, "Missing");
            let missing_facts = checked(tcx, "Missing");
            let missing_pat = binding(tcx, missing, "inferred");
            assert!(missing_facts
                .bindings
                .mode_for(
                    tcx,
                    missing,
                    missing,
                    tcx.hir_body_owned_by(missing),
                    missing_pat
                )
                .is_err());
            assert!(facts
                .bindings
                .mode_for(tcx, assigned, assigned, body, missing_pat)
                .is_err());
            assert!(facts
                .bindings
                .mode_for(tcx, missing, assigned, body, original)
                .is_err());
            let proof = named(tcx, "ProofOnly");
            assert_eq!(
                checked(tcx, "ProofOnly")
                    .bindings
                    .mode_for(
                        tcx,
                        proof,
                        proof,
                        tcx.hir_body_owned_by(proof),
                        binding(tcx, proof, "inferred")
                    )
                    .unwrap(),
                Mode::Proof
            );
            for (name, tag) in [
                ("Missing", "binding-modes"),
                ("Initialized", "infer-mode"),
                ("Literal", "binding-modes"),
            ] {
                let record = read
                    .fns
                    .iter()
                    .find(|record| record.def_id == named(tcx, name))
                    .unwrap();
                assert!(
                    matches!(&record.status, crate::reader::FnStatus::Refused(refusal) if refusal.tag == tag),
                    "{name}: {:?}",
                    record.status
                );
            }
            // The existing parameter ownership gate may precede the inference
            // gate; neither may turn the completed Proof mode into a receipt.
            let record = read
                .fns
                .iter()
                .find(|record| record.def_id == proof)
                .unwrap();
            assert!(
                matches!(&record.status, crate::reader::FnStatus::Refused(refusal)
            if matches!(refusal.tag, "param-mode" | "infer-mode-ownership")),
                "{:?}",
                record.status
            );
            assert!(!read.native_ownership.contains(&proof));
            for name in ["SpecEscape", "Incompatible"] {
                let owner = named(tcx, name);
                assert!(
                    read.errors.iter().any(|error| error.function == Some(owner)
                        && error.phase == crate::messages::Phase::Modes),
                    "{name}: {:?}",
                    read.errors
                );
                let record = read
                    .fns
                    .iter()
                    .find(|record| record.def_id == owner)
                    .unwrap();
                assert!(
                    matches!(record.status, crate::reader::FnStatus::Rejected),
                    "{name}: {:?}",
                    record.status
                );
            }
            for name in ["Initialized", "Literal"] {
                assert!(
                    matches!(
                        modes::check_with_context(
                            &Context(DeclarationModes::new(tcx)),
                            named(tcx, name)
                        ),
                        modes::ModeCheck::Unknown(_)
                    ),
                    "{name}"
                );
            }
            let generated = trust_vc_vcir::vcgen::generate(&read.krate);
            let assigned_fn = function(tcx, read, "Assigned");
            assert!(
                matches!(generated.get(assigned_fn.id), Some(FnVcs::Checks(checks)) if checks.is_empty())
            );
        },
        false,
    );
}
