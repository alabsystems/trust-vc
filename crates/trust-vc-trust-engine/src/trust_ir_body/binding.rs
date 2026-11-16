// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Provisional binding of a body-lane verdict to the trust-ir it was computed
//! from.
//!
//! `Module::stable_digest` hashes the proof tables, so a digest of the whole
//! module goes stale the moment a verdict is written back; and
//! `Module::obligation_digest` needs trust-ir's `fmt` feature, which this
//! crate does not enable. The lane therefore digests a STRIPPED clone: the
//! target function alone, with every proof, status, certificate, diagnostic
//! and debug-location field cleared, and every type, struct, enum, record,
//! closure, global, function-type, predicate, spec and universe table (plus
//! `target_info`) kept. This is local and provisional until trust-ir defines
//! a semantic body digest of its own.
//!
//! Two deliberate imprecisions, both conservative — they can make a binding go
//! stale when it need not, never make a stale binding look fresh:
//!
//! * `Function::summary`'s `requires`/`ensures` are producer spec STRINGS and
//!   are KEPT, so rewording a clause moves the digest without touching the
//!   body. The lane never reads them as facts (they are flagged in
//!   `IgnoredInputs`); keeping them in the digest is the fail-closed choice
//!   while the strip list is hand-maintained.
//! * The digest covers the BODY, not which reading of it was decided. The
//!   reading is carried separately on [`TrustIrBodyBinding::reading`], and is
//!   part of [`TrustIrBodyBinding::canonical_string`], hence of the
//!   certificate's `unit_id`.

use std::fmt::Write as _;

use sha2::{Digest, Sha256};
use trust_ir::{FuncId, Module, ObligationSite, ProofDigestAlgorithm, ProofId};

use super::TrustIrBodyError;

/// Schema of the provisional binding.
pub const TRUST_IR_BODY_BINDING_SCHEMA: &str = "trust-vc.trust-ir-body.binding.v0-provisional";

/// The trust-ir revision the lane was written and measured against: the one
/// this workspace's `Cargo.lock` pins, with the wire version of that trust-ir
/// (`tests/trust_ir_pin_label.rs` checks both). A superproject that patches in
/// another trust-ir links that one, and its IR cohort check compares the two.
pub const TRUST_IR_BODY_TRUST_IR_PIN: &str =
    "trust-ir 0.14.0@ba039cfea77ae44eeaba0dc8e2946c27d5d97ddd bin v74";

const SEMANTIC_DIGEST_DOMAIN: &str = "trust-vc.trust_ir_body.semantic.v0";

/// Why a module has no canonical binary image, and so no `stable_digest`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WireIdentityGap {
    /// Where the construct sits, e.g. `function 'f' bb0 #3`.
    pub(crate) location: String,
    /// What it is, in trust-ir's own words.
    pub(crate) construct: String,
}

/// Claims whose SOURCE module must be refused before any proof-row projection.
/// These probes are available in ordinary trust-ir core feature configurations;
/// no binary feature, substitute digest, or claim erasure is involved.
fn nonwire_claim_gap(module: &Module) -> Option<WireIdentityGap> {
    if module.completeness_claim_unencodable() {
        return Some(WireIdentityGap {
            location: "module".to_string(),
            construct: "Module.completeness".to_string(),
        });
    }
    module
        .first_certificate_binding()
        .map(|(certificate, obligation)| WireIdentityGap {
            location: format!(
                "certificate #{certificate} for obligation #{}",
                obligation.index()
            ),
            construct: "CleanCicKernelRecheck.binding (CertificateBinding)".to_string(),
        })
}

/// The first construct in `module` that trust-ir's canonical binary writer
/// cannot encode, if any.
///
/// The writer PANICS on such a construct rather than inventing a tag byte, so
/// `Module::stable_digest` of a module carrying one aborts the process. At
/// trust-ir `0.14.0@4f09dab8` that is every `Inst::binary_wire_gap`
/// (`MakeAggregate`, the bulk-memory pair `MemCopy`/`MemSet`, and the
/// `CtLz`/`CtTz`/`BSwap`/`BitReverse` and `RotL`/`RotR`/`FCopySign` sub-ops)
/// and a lexical scope's inlining-chain link. At the R297 cohort, completeness
/// claims and bound certificate directives also have no binary carrier. This
/// consults the same upstream core probes as `trust_ir_build::wire_identity_blocker`.
///
/// Every `stable_digest` this crate takes of a CALLER-SUPPLIED module is
/// preceded by this probe, so such a module is refused BY NAME instead of
/// taking the verifier down mid-verdict. This is a bounded carrier preflight,
/// not a claim that every malformed module is panic-free.
pub(crate) fn wire_identity_gap(module: &Module) -> Option<WireIdentityGap> {
    if let Some(gap) = nonwire_claim_gap(module) {
        return Some(gap);
    }
    for function in &module.functions {
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if let Some(construct) = node.inst.binary_wire_gap() {
                    return Some(WireIdentityGap {
                        location: format!(
                            "function '{}' bb{} #{index}",
                            function.name,
                            block.id.index()
                        ),
                        construct: construct.to_string(),
                    });
                }
            }
        }
    }
    module
        .first_inlined_scope_chain()
        .map(|(function, scope)| WireIdentityGap {
            location: format!("function #{function} scope #{scope}"),
            construct: "a lexical scope's inlining-chain link (ScopeData.inlined_at) ahead \
                        of its binary carrier"
                .to_string(),
        })
}

/// Digest of `function`'s semantics inside `module`, independent of every
/// proof-status, certificate and debug-metadata field.
///
/// Refused with [`TrustIrBodyError::NoWireIdentity`] when the function's image
/// carries a construct trust-ir's binary writer cannot encode (see
/// [`wire_identity_gap`]): no digest exists to bind a verdict to, so none is
/// made. Completeness and bound-certificate claims are checked on the original
/// module before this function's provisional proof/debug-metadata projection.
pub fn trust_ir_body_semantic_digest(
    module: &Module,
    function: FuncId,
) -> Result<String, TrustIrBodyError> {
    match module
        .functions
        .iter()
        .filter(|candidate| candidate.id == function)
        .count()
    {
        0 => return Err(TrustIrBodyError::FunctionMissing(function)),
        1 => {}
        _ => return Err(TrustIrBodyError::FunctionDuplicated(function)),
    }
    // Check source claims BEFORE clearing proof rows. In contrast to ordinary
    // unbound evidence, a bound directive cannot silently disappear into this
    // provisional semantic projection. Keep the existing function-isolation
    // and ordinary debug/proof-metadata stripping behavior below unchanged.
    if let Some(gap) = nonwire_claim_gap(module) {
        return Err(TrustIrBodyError::NoWireIdentity {
            function,
            location: gap.location,
            construct: gap.construct,
        });
    }
    let mut stripped = module.clone();
    stripped
        .functions
        .retain(|candidate| candidate.id == function);
    stripped.proof_obligations.clear();
    stripped.proof_certificates.clear();
    stripped.obligation_diagnostics.clear();
    stripped.files.clear();
    for target in &mut stripped.functions {
        target.proofs.clear();
        if let Some(summary) = target.summary.as_mut() {
            summary.proved = false;
        }
        target.source_provenance = None;
        target.value_names = None;
        target.scopes = None;
        for block in &mut target.blocks {
            for node in &mut block.body {
                node.proofs.clear();
                node.span = None;
                node.scope = None;
            }
        }
    }
    if let Some(gap) = wire_identity_gap(&stripped) {
        return Err(TrustIrBodyError::NoWireIdentity {
            function,
            location: gap.location,
            construct: gap.construct,
        });
    }
    let module_digest = stripped.stable_digest();
    let mut hasher = Sha256::new();
    hasher.update(SEMANTIC_DIGEST_DOMAIN.as_bytes());
    hasher.update([0u8]);
    hasher.update(function.index().to_be_bytes());
    hasher.update([match module_digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0u8,
        ProofDigestAlgorithm::TrustIrStableV1 => 1u8,
    }]);
    hasher.update(module_digest.bytes);
    let mut out = String::from("sha256:");
    for byte in hasher.finalize() {
        let _ = write!(&mut out, "{byte:02x}");
    }
    Ok(out)
}

/// What an advisory body-lane verdict is about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrBodyBinding {
    pub schema: &'static str,
    pub trust_ir: &'static str,
    pub semantic_digest: String,
    pub function: FuncId,
    pub site: ObligationSite,
    pub proof_id: ProofId,
    pub kind: String,
    /// Which semantics the certified query is about. Part of
    /// [`Self::canonical_string`], hence of the artifact's `unit_id`, so it
    /// cannot be dropped while keeping the certificate.
    pub reading: super::BodyReading,
}

impl TrustIrBodyBinding {
    /// One-line canonical rendering; used as the certificate's `unit_id`.
    pub fn canonical_string(&self) -> String {
        format!(
            "{}|{}|{}|fn={}|site=fn{}:bb{}:i{}|proof={}|kind={}|reading={}",
            self.schema,
            self.trust_ir,
            self.semantic_digest,
            self.function.index(),
            self.site.function.index(),
            self.site.block.index(),
            self.site.inst_index,
            self.proof_id.index(),
            self.kind,
            match self.reading {
                super::BodyReading::PinnedInterpreter => "pinned-interpreter",
                super::BodyReading::HavocInstantiatedUndef => "havoc-instantiated-undef",
            }
        )
    }
}

/// An Alethe artifact for one discharged site. `report_only` is always
/// `true` and `lowering_witness` always `"none"`: nothing independent has
/// re-checked that the solver query is the site's meaning.
#[cfg(feature = "proof-certificates")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrBodyCertificate {
    pub binding: TrustIrBodyBinding,
    pub artifact: crate::TrustReplayableProofArtifact,
    pub report_only: bool,
    pub lowering_witness: &'static str,
}

/// Uninhabited without `proof-certificates`: the certificate slot is always
/// `None` in that build.
#[cfg(not(feature = "proof-certificates"))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustIrBodyCertificate {}
