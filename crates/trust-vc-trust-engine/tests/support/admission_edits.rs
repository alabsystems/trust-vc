// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Edits of the admission baseline that no honest producer writes: a
//! certificate term that is no proof, and a replay atom that forges its
//! certificate's assertion id or formula. Included with `#[path]` beside `admission_baseline.rs`,
//! whose module it uses; not a test target itself.

#![allow(dead_code)]

use super::admission_baseline::{
    assertion_atoms_mut, reseal_clean_cic_lineage, reseal_module_identity,
    set_compiler_fact_assertion_id,
};
use trust_ir::request::{
    NativeAssertionId, NativeReplayAtomKind, NativeVerificationBundle, NativeVerificationRequest,
};
use trust_ir::{ProofEvidence, ProofFormula, ProofId};
use trust_vc_trust_engine::{TrustEngineError, TrustVcTrustEngine};

/// LIAR L1: every `Assertion` atom of TrustVc request `request_index` citing
/// `obligation_id` claims assertion id `forged`, and the request is resealed —
/// its digest recomputed and re-copied into its evidence bundle — so the only
/// lie is the id. trust-ir refuses it at the door
/// (`ReplayAtomAssertionMismatch`).
pub fn forge_atom_id(
    bundle: &mut NativeVerificationBundle,
    request_index: usize,
    obligation_id: ProofId,
    forged: u32,
) {
    let atoms = assertion_atoms_mut(bundle, request_index, obligation_id);
    assert!(
        !atoms.is_empty(),
        "no atom cites obligation {obligation_id:?}"
    );
    for atom in atoms {
        atom.assertion_id = Some(NativeAssertionId::new(forged));
    }
    reseal_module_identity(bundle);
}

/// LIAR L3: every `Assertion` atom of TrustVc request `request_index` citing
/// `obligation_id` asserts `formula` instead of its obligation's, its payload
/// digest recomputed and the request resealed, so the only lie is the formula.
/// trust-ir-build never compares atom formulas for a kernel-replayed
/// certificate, so only trust-vc's input gate can refuse it.
pub fn forge_atom_formula(
    bundle: &mut NativeVerificationBundle,
    request_index: usize,
    obligation_id: ProofId,
    formula: ProofFormula,
) {
    let atoms = assertion_atoms_mut(bundle, request_index, obligation_id);
    assert!(
        !atoms.is_empty(),
        "no atom cites obligation {obligation_id:?}"
    );
    for atom in atoms {
        atom.formula = formula.clone();
        atom.payload_digest = atom.expected_payload_digest();
    }
    reseal_module_identity(bundle);
}

/// A formula that is not `formula`: the SMT-LIB text `(>= 0 5)` (false, where
/// the corpus states `(>= 5 0)`), or `(>= 0 6)` if that is what `formula`
/// already states.
pub fn another_formula(formula: &ProofFormula) -> ProofFormula {
    let text = if formula.payload == "(>= 0 5)" {
        "(>= 0 6)"
    } else {
        "(>= 0 5)"
    };
    ProofFormula {
        schema: "smtlib2".to_string(),
        payload: text.to_string(),
        smtlib: Some(text.to_string()),
        sort: Some("Bool".to_string()),
        bindings: Vec::new(),
    }
}

/// ROUND 13: gives every obligation in `obligations` the assertion identity
/// (`string`, `number`) — its own `source.assertion_id`, its compiler-fact
/// number, and the id of every TrustVc atom citing it — then re-derives each
/// one's CleanCic lineage (it covers the source identity) and reseals. Every
/// rendering of each obligation agrees with every other, so no input gate
/// sees a disagreement; the only lie is that two obligations are one
/// assertion (or that one is another's).
pub fn relabel_assertion_identity(
    bundle: &mut NativeVerificationBundle,
    obligations: &[ProofId],
    string: &str,
    number: u32,
) {
    for &obligation_id in obligations {
        bundle
            .module
            .proof_obligations
            .iter_mut()
            .find(|obligation| obligation.id == obligation_id)
            .expect("obligation exists")
            .source
            .as_mut()
            .expect("corpus obligations carry a source identity")
            .assertion_id = string.to_string();
        set_compiler_fact_assertion_id(bundle, obligation_id, number);
        reseal_clean_cic_lineage(bundle, obligation_id);
    }
    reseal_module_identity(bundle);
}

/// ROUND 13, THE BLOCKER PROBE: `thief` takes `victim`'s whole assertion
/// identity (its string, its compiler-fact number, and that number on
/// `thief`'s atom), and the bundle is resealed. Returns the stolen number.
pub fn steal_assertion_identity(
    bundle: &mut NativeVerificationBundle,
    thief: ProofId,
    victim: ProofId,
) -> u32 {
    let string = bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == victim)
        .and_then(|obligation| obligation.source.as_ref())
        .expect("the victim carries a source identity")
        .assertion_id
        .clone();
    let number = bundle
        .compiler_facts
        .obligation_source(victim)
        .and_then(|source| source.assertion_id)
        .expect("the victim carries a compiler-fact number")
        .index();
    relabel_assertion_identity(bundle, &[thief], &string, number);
    number
}

/// THE LIAR TWINS OF AN ADMISSION. For every `Assertion` atom that states an id
/// in every TrustVc request of `admitted`, two edited copies must each be
/// REFUSED by the consumer:
///
/// * L1, the atom's id forged (moved off the compiler fact's number), which
///   trust-ir refuses at the door;
/// * L3, the atom asserting another formula than its obligation, which only
///   trust-vc's input gate sees.
///
/// Returns how many atoms were forged, so a caller can assert it forged some.
#[track_caller]
pub fn assert_id_and_formula_liars_refused(admitted: &NativeVerificationBundle) -> usize {
    let engine = TrustVcTrustEngine::new();
    let mut forged = 0usize;
    for (request_index, request) in admitted.requests.iter().enumerate() {
        let NativeVerificationRequest::TrustVc(request) = request else {
            continue;
        };
        for atom in &request.provenance.replay_context.atoms {
            let (NativeReplayAtomKind::Assertion, Some(obligation), Some(assertion_id)) =
                (atom.kind, atom.obligation, atom.assertion_id)
            else {
                continue;
            };
            forged += 1;

            let mut forged_id = admitted.clone();
            forge_atom_id(
                &mut forged_id,
                request_index,
                obligation,
                assertion_id.index().wrapping_add(1000),
            );
            let error = engine
                .consume_native_trust_ir_bundle(&forged_id)
                .expect_err("L1: an atom whose id was forged must be refused");
            assert!(
                error.to_string().contains("assertion id"),
                "L1 refused for the forged id, not for something else: {error}"
            );

            let mut forged_formula = admitted.clone();
            forge_atom_formula(
                &mut forged_formula,
                request_index,
                obligation,
                another_formula(&atom.formula),
            );
            let error = engine
                .consume_native_trust_ir_bundle(&forged_formula)
                .expect_err("L3: an atom asserting another formula must be refused");
            assert!(
                matches!(
                    error,
                    TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { .. }
                ),
                "L3 is refused by trust-vc's own atom gate: {error}"
            );
        }
    }
    forged
}

/// Corrupts certificate 0's CleanCic proof TERM — the constant `true` renamed —
/// and rewrites every reference to the certificate by value. It stays
/// non-empty and lineage-bound and is no longer a proof of anything, so on a
/// `Certified` obligation the in-process Clean-kernel re-check fails. (The
/// corpus's own term re-checks.)
pub fn corrupt_clean_cic_term(bundle: &mut NativeVerificationBundle) {
    let previous = bundle.module.proof_certificates[0].lineage_ref();
    let ProofEvidence::CleanCic { term, .. } = &mut bundle.module.proof_certificates[0].evidence
    else {
        panic!("the corpus certificate 0 should be CleanCic");
    };
    let at = term
        .windows(4)
        .position(|window| window == b"true")
        .expect("the corpus term names the constant `true`");
    term[at..at + 4].copy_from_slice(b"fals");
    let current = bundle.module.proof_certificates[0].lineage_ref();
    for node in &mut bundle.lineage.nodes {
        for certificate in &mut node.certificates {
            if *certificate == previous {
                *certificate = current.clone();
            }
        }
    }
    for request in &mut bundle.requests {
        if let NativeVerificationRequest::TrustVc(request) = request {
            for certificate in &mut request.certificates {
                if *certificate == previous {
                    *certificate = current.clone();
                }
            }
        }
    }
    reseal_module_identity(bundle);
}
