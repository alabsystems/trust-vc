//! Capability #2 — compiler-fact frame/alias VCs from Trust's compiler IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verus reasons about framing from *surface* `ensures`/`opens_invariants`
//! clauses the user writes; it has no view of rustc's resolved ownership and
//! borrow lineage. Trust *does*: its compiler IR ([`trust_ir`]) carries
//! [`trust_ir::NativeCompilerFactRef`]s — typed references to facts rustc
//! already resolved (ADT layout, fat-pointer/trait-object metadata, pointer
//! offsets, casts, monomorphization). This module lowers a **frame view** of
//! those facts into a [`DriverFn`] whose postconditions are the frame
//! conditions, then discharges them through the real encoder + ay solver.
//!
//! A frame condition is the classic separation-logic obligation: for every
//! location `y` *not* in the set of locations a call modifies, `y` is preserved
//! (`y_post == y_pre`). The compiler supplies the modified set; we encode the
//! preservation of everything outside it and let the backend either prove it
//! (when the body relation truly only touches the modified set) or refute it
//! with a counterexample (when an "unmodified" claim is actually violated).
//!
//! ## Mapping from `trust_ir::NativeCompilerFactRef`
//!
//! [`trust_ir::NativeObligationSource`] attaches a `Vec<NativeCompilerFactRef>`
//! to each obligation, where (from `../trust-ir/.../request.rs`):
//!
//! ```text
//! pub enum NativeCompilerFactRef {
//!     AdtLayout(NativeCompilerFactId),
//!     FatPointer(NativeCompilerFactId),
//!     TraitObjectMetadata(NativeCompilerFactId),
//!     PointerOffset(NativeCompilerFactId),
//!     Cast(NativeCompilerFactId),
//!     Monomorphization(NativeMonomorphizationId),
//! }
//! ```
//!
//! Each variant carries the *identity* of a resolved compiler fact; the fact
//! payloads (e.g. which fields/places a layout or offset touches) live in
//! [`trust_ir::NativeCompilerFacts`] and are consumed, validated, and bound to
//! obligations by `crates/trust-vc-trust-engine/src/native_trust_ir_bundle.rs`
//! (see `TrustVcNativeCompilerFactsBinding` /
//! `validate_native_trust_ir_bundle`). That engine boundary already owns
//! decoding the full bundle; this module takes the *post-resolution* view — the
//! set of modified location names a frame obligation depends on — and turns it
//! into a checked VC. [`FrameFact::from_fact_ref`] records which
//! `NativeCompilerFactRef` justifies a given modified location, so the produced
//! [`DriverFn`] is traceable back to compiler lineage rather than a re-derived
//! surface spec.
//!
//! Fail-closed: the frame VC only *asserts* preservation of locations the
//! caller declares unmodified, and only *assumes* the body relation the caller
//! supplies. Nothing here makes a violated frame condition pass — a modified
//! location claimed unmodified is refuted by the solver.

use crate::lower::{Binding, DriverFn};
use trust_vc_core::ir::{CompareOp, TrustVcExpr, TrustVcType};

#[cfg(feature = "trust-integration")]
use trust_ir::request::NativeCompilerFactRef;

/// A `pre`/`post` pair of typed locations: one SMT variable for the value of a
/// location on entry, one for its value on exit. Frame conditions are stated
/// over these pairs.
#[derive(Debug, Clone)]
pub struct FrameLoc {
    /// Base location name (e.g. a place/local name from MIR).
    pub name: String,
    /// Location type (resolved; from `TyCtxt` in the driver path).
    pub ty: TrustVcType,
}

impl FrameLoc {
    /// A typed frame location.
    pub fn new(name: impl Into<String>, ty: TrustVcType) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }

    /// The entry-value binding (`<name>_pre`).
    #[must_use]
    pub fn pre(&self) -> Binding {
        Binding::new(format!("{}_pre", self.name), self.ty.clone())
    }

    /// The exit-value binding (`<name>_post`).
    #[must_use]
    pub fn post(&self) -> Binding {
        Binding::new(format!("{}_post", self.name), self.ty.clone())
    }
}

/// The compiler's resolved frame view for one call/region: the set of location
/// names the call may modify, optionally each justified by the
/// [`NativeCompilerFactRef`] that established it.
///
/// The modified set is the *write footprint* rustc resolved; everything outside
/// it is, by the borrow/ownership facts, preserved. That preservation is what
/// [`lower_frame`] turns into checked postconditions.
#[derive(Debug, Clone, Default)]
pub struct FrameFact {
    /// Names of locations the call may modify (its write footprint).
    pub modified: Vec<String>,
    /// Parallel justification: which compiler fact established each modified
    /// entry, when sourced from a real bundle. Empty when modeled directly.
    #[cfg(feature = "trust-integration")]
    pub justifications: Vec<NativeCompilerFactRef>,
}

impl FrameFact {
    /// A frame fact from a modified-location set (modeled / test path).
    pub fn new(modified: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self {
            modified: modified.into_iter().map(Into::into).collect(),
            #[cfg(feature = "trust-integration")]
            justifications: Vec::new(),
        }
    }

    /// Records that `location` is modified, justified by a real compiler fact
    /// reference [`NativeCompilerFactRef`] resolved by rustc. This is the entry
    /// point that ties a frame obligation to compiler borrow/ownership lineage
    /// rather than a re-derived surface spec.
    #[cfg(feature = "trust-integration")]
    pub fn from_fact_ref(
        mut self,
        location: impl Into<String>,
        fact: NativeCompilerFactRef,
    ) -> Self {
        self.modified.push(location.into());
        self.justifications.push(fact);
        self
    }

    /// True if `name` is in the modified (write-footprint) set.
    #[must_use]
    pub fn modifies(&self, name: &str) -> bool {
        self.modified.iter().any(|m| m == name)
    }
}

/// Lowers a frame view into a frame-condition [`DriverFn`].
///
/// `locs` are the typed locations in scope; `fact` is the compiler-resolved
/// write footprint; `body` is the relational body assumption the caller
/// supplies (typically `loc_post == <new value>` for each modified location and
/// `loc_post == loc_pre` for each preserved location — the relation rustc's
/// facts justify). The produced function:
///
/// * declares `<name>_pre` and `<name>_post` for every location,
/// * assumes the supplied `body` relations,
/// * for every location **not** in `fact.modified`, asserts the frame condition
///   `<name>_post == <name>_pre`.
///
/// `result` is a synthetic unit-ish marker (the frame VC has no return value);
/// it is required only because [`DriverFn`] carries a result binding. We reuse
/// the first preserved location's type, or `bool` if none, and never reference
/// it in an obligation — its presence is inert.
#[must_use]
pub fn lower_frame(
    name: &str,
    locs: &[FrameLoc],
    fact: &FrameFact,
    body: Vec<TrustVcExpr>,
) -> DriverFn {
    // Pre/post params for every location.
    let mut params: Vec<Binding> = Vec::with_capacity(locs.len() * 2);
    for loc in locs {
        params.push(loc.pre());
        params.push(loc.post());
    }

    // Frame postconditions: preserved locations stay equal.
    let ensures: Vec<TrustVcExpr> = locs
        .iter()
        .filter(|loc| !fact.modifies(&loc.name))
        .map(frame_eq)
        .collect();

    // Inert synthetic result (never referenced by any obligation).
    let result = Binding::new(
        format!("{name}__frame_unit"),
        locs.first()
            .map(|l| l.ty.clone())
            .unwrap_or(TrustVcType::Bool),
    );

    DriverFn {
        name: name.to_string(),
        params,
        result,
        // The body relation is the assumption; encode it via `requires` so each
        // relation is assumed independently (the body_value slot is a single
        // `result == ...` equality, which does not fit a multi-relation frame).
        requires: body,
        body_value: None,
        ensures,
    }
}

/// The frame equality `<loc>_post == <loc>_pre`.
fn frame_eq(loc: &FrameLoc) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(loc.post().as_var()),
        right: Box::new(loc.pre().as_var()),
    }
}

/// Convenience: the relation `<loc>_post == <loc>_pre` as a *body assumption*
/// (the compiler-justified fact that a location was preserved).
#[must_use]
pub fn assume_preserved(loc: &FrameLoc) -> TrustVcExpr {
    frame_eq(loc)
}

/// Convenience: the relation `<loc>_post == rhs` as a body assumption (the
/// compiler-justified fact that a location was written with a new value).
#[must_use]
pub fn assume_written(loc: &FrameLoc, rhs: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(loc.post().as_var()),
        right: Box::new(rhs),
    }
}

/// Carry an ay/kernel proof certificate into Trust's compiler-IR proof lineage.
///
/// trust-vc's [`crate::lower::Certificate`] (an ay UNSAT/Alethe proof
/// independently re-checked by `trust-vc-kernel`) maps directly onto a
/// [`trust_ir::ProofCertificate`]: the Alethe text becomes
/// [`trust_ir::ProofEvidence::SmtProof`] — *re-checkable* evidence (not a trusted
/// answer) — under the `trust-vc/ay` prover, bound to the obligation id. This
/// realizes the north-star claim that trust-vc emits `trust_ir::ProofCertificate`
/// back to Trust, the soundness edge Verus's artifact-free black-box Z3 cannot
/// provide. Available when both the `certificates` and `trust-integration`
/// features are enabled.
#[cfg(feature = "certificates")]
#[must_use]
pub fn certificate_to_trust_ir(
    cert: &crate::lower::Certificate,
    obligation_id: u32,
) -> trust_ir::ProofCertificate {
    trust_ir::ProofCertificate {
        obligation: trust_ir::ProofId::new(obligation_id),
        prover: if cert.kernel_verified {
            "trust-vc/ay (kernel-verified)".to_string()
        } else {
            "trust-vc/ay".to_string()
        },
        evidence: trust_ir::ProofEvidence::SmtProof(cert.alethe.clone().into_bytes()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::uint;

    #[cfg(feature = "certificates")]
    #[test]
    fn ay_certificate_maps_to_trust_ir_proof_certificate() {
        use crate::lower::{add, cmp, lit, var, Binding, DriverFn, Outcome};
        use trust_vc_core::ir::CompareOp;
        let u = uint(32);
        let f = DriverFn {
            name: "add_bounds".into(),
            params: vec![Binding::new("x", u.clone()), Binding::new("y", u.clone())],
            result: Binding::new("result", u.clone()),
            requires: vec![
                cmp(CompareOp::Lt, var("x", u.clone()), lit(100, u.clone())),
                cmp(CompareOp::Lt, var("y", u.clone()), lit(100, u.clone())),
            ],
            body_value: Some(add(var("x", u.clone()), var("y", u.clone()), u.clone())),
            ensures: vec![cmp(CompareOp::Lt, var("result", u.clone()), lit(200, u))],
        };
        let certified = f.verify_certified();
        assert_eq!(certified.outcome, Outcome::Verified);
        let cert = certified
            .certificate
            .expect("verified result carries a certificate");
        let pc = certificate_to_trust_ir(&cert, 42);
        assert_eq!(pc.obligation, trust_ir::ProofId::new(42));
        assert!(pc.prover.contains("trust-vc/ay"));
        match pc.evidence {
            trust_ir::ProofEvidence::SmtProof(bytes) => {
                assert!(
                    !bytes.is_empty(),
                    "Alethe proof carried as SmtProof evidence"
                )
            }
            other => panic!("expected SmtProof evidence, got {other:?}"),
        }
    }

    #[test]
    fn frame_fact_tracks_modified_set() {
        let f = FrameFact::new(["counter"]);
        assert!(f.modifies("counter"));
        assert!(!f.modifies("other"));
    }

    #[test]
    fn preserved_locations_become_ensures_modified_do_not() {
        let x = FrameLoc::new("x", uint(32));
        let y = FrameLoc::new("y", uint(32));
        // Only `x` is modified; `y` is preserved.
        let fact = FrameFact::new(["x"]);
        let df = lower_frame(
            "frame_xy",
            &[x.clone(), y.clone()],
            &fact,
            vec![assume_written(&x, x.pre().as_var()), assume_preserved(&y)],
        );
        // 2 locations * (pre,post) = 4 params.
        assert_eq!(df.params.len(), 4);
        // Exactly one preserved location (`y`) yields one frame ensures.
        assert_eq!(df.ensures.len(), 1);
    }
}
