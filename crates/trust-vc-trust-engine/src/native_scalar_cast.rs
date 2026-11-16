//! Same-run original-input binding for actual native scalar-cast emissions.
//!
//! These values retain what the existing producer and solver did. They are
//! data for a separate canonical translation check, never a proof of that
//! translation and never a source, ABI, or proof-grade authority.

use std::cell::RefCell;
use std::sync::Arc;

use serde::Serialize;
use trust_ir::inst::CastOp;
use trust_ir::request::NativeVerificationBundle;
use trust_ir::Ty;
use trust_vc_core::scalar_cast_capture::ScalarCastCaptureData;

use crate::{
    TrustEngineError, TrustExpr, TrustVcNativeTrustIrBundleReport,
    TrustVcNativeTrustIrProducedCertificate, TrustVcTrustEngine, TrustVerificationRequest,
};

const MAX_ORIGINAL_BYTES: usize = 16 * 1024 * 1024;

/// A site read by the existing native instruction lowering itself.
#[derive(Debug, Clone)]
pub struct ScalarCastSite {
    pub function: u32,
    pub block: u32,
    pub instruction: usize,
    pub opcode: CastOp,
    pub source_type: Ty,
    pub destination_type: Ty,
    pub operand: u32,
    pub result: u32,
    pub assumption_id: String,
    pub definition: TrustExpr,
}

/// Original inputs, same-run certificate and actual encoding, with no public
/// constructor or deserializer. This establishes provenance of the data only.
#[derive(Debug)]
pub struct NativeScalarCastBinding {
    original_bundle: Arc<[u8]>,
    original_module: Arc<[u8]>,
    request_id: u32,
    function_id: u32,
    obligation_id: u32,
    certificate: TrustVcNativeTrustIrProducedCertificate,
    typed_request: TrustVerificationRequest,
    sites: Vec<ScalarCastSite>,
    encoding: ScalarCastCaptureData,
}

impl NativeScalarCastBinding {
    pub fn original_bundle_bytes(&self) -> &[u8] {
        &self.original_bundle
    }
    pub fn original_module_bytes(&self) -> &[u8] {
        &self.original_module
    }
    pub const fn request_id(&self) -> u32 {
        self.request_id
    }
    pub const fn function_id(&self) -> u32 {
        self.function_id
    }
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }
    pub fn certificate(&self) -> &TrustVcNativeTrustIrProducedCertificate {
        &self.certificate
    }
    pub fn typed_request(&self) -> &TrustVerificationRequest {
        &self.typed_request
    }
    pub fn sites(&self) -> &[ScalarCastSite] {
        &self.sites
    }
    pub fn encoding(&self) -> &ScalarCastCaptureData {
        &self.encoding
    }

    /// Compare the complete original input and exact produced certificate,
    /// including fields the semantic digests intentionally do not cover.
    /// Equality is not a translation theorem or a new admission policy.
    pub fn matches(
        &self,
        bundle: &NativeVerificationBundle,
        certificate: &TrustVcNativeTrustIrProducedCertificate,
    ) -> bool {
        bounded_json(bundle).is_ok_and(|bytes| bytes.as_slice() == &*self.original_bundle)
            && bounded_json(certificate)
                .and_then(|actual| {
                    bounded_json(&self.certificate).map(|expected| actual == expected)
                })
                .unwrap_or(false)
            && certificate.request_id() == self.request_id
            && certificate.obligation_id() == self.obligation_id
    }
}

/// The unchanged native report plus observations for newly produced proofs.
#[derive(Debug)]
pub struct NativeScalarCastVerification {
    report: TrustVcNativeTrustIrBundleReport,
    bindings: Vec<Result<NativeScalarCastBinding, String>>,
}
impl NativeScalarCastVerification {
    pub fn report(&self) -> &TrustVcNativeTrustIrBundleReport {
        &self.report
    }
    pub fn bindings(&self) -> &[Result<NativeScalarCastBinding, String>] {
        &self.bindings
    }
}

impl TrustVcTrustEngine {
    /// Verify the full original bundle once using existing admission and proof
    /// policies. Missing or refused observations preserve native-only results.
    pub fn consume_native_trust_ir_bundle_with_scalar_cast_bindings(
        &self,
        bundle: &NativeVerificationBundle,
    ) -> Result<NativeScalarCastVerification, TrustEngineError> {
        let original_bundle = bounded_json(bundle).map(Arc::from);
        let original_module = original_bundle
            .as_ref()
            .map_err(Clone::clone)
            .and_then(|_| {
                trust_ir::binary::serialize_module(&bundle.module)
                    .map_err(|error| error.to_string())
                    .and_then(|bytes| {
                        if bytes.len() > MAX_ORIGINAL_BYTES {
                            Err("original module exceeds cast binding bound".into())
                        } else {
                            Ok(Arc::from(bytes))
                        }
                    })
            });
        if let Some(reason) = original_bundle
            .as_ref()
            .err()
            .or(original_module.as_ref().err())
        {
            let report = self.consume_native_trust_ir_bundle(bundle)?;
            return Ok(NativeScalarCastVerification {
                report,
                bindings: vec![Err(reason.clone())],
            });
        }
        let sink = ObservationSink {
            original_bundle,
            original_module,
            bindings: RefCell::new(Vec::new()),
        };
        let report = self.consume_native_trust_ir_bundle_observing(bundle, Some(&sink))?;
        Ok(NativeScalarCastVerification {
            report,
            bindings: sink.bindings.into_inner(),
        })
    }
}

pub(crate) struct UnitCastObservation {
    pub request: TrustVerificationRequest,
    pub encoding: ScalarCastCaptureData,
}

pub(crate) struct ObservationSink {
    original_bundle: Result<Arc<[u8]>, String>,
    original_module: Result<Arc<[u8]>, String>,
    bindings: RefCell<Vec<Result<NativeScalarCastBinding, String>>>,
}
impl ObservationSink {
    pub(crate) fn record(
        &self,
        request_id: u32,
        function_id: u32,
        obligation_id: u32,
        sites: Option<Vec<ScalarCastSite>>,
        certificate: &TrustVcNativeTrustIrProducedCertificate,
        observation: Option<Result<UnitCastObservation, String>>,
    ) {
        // No translation question is promised when the original body has no cast.
        if sites.as_ref().is_some_and(Vec::is_empty) {
            return;
        }
        let binding = (|| {
            let sites = sites.ok_or("original cast site inventory exceeds its bound")?;
            bounded_json(certificate)?;
            let original_bundle = self.original_bundle.clone()?;
            let original_module = self.original_module.clone()?;
            let observation =
                observation.ok_or("native proof has no same-run cast observation")??;
            // Match source definitions against ORIGINAL typed roots from the
            // real encoding. Preparation must also preserve this native
            // fragment; a substitution requiring another theorem refuses here.
            for site in &sites {
                let expected = site
                    .definition
                    .to_trust_vc_expr()
                    .map_err(|e| e.to_string())?;
                let matching = observation
                    .encoding
                    .conditions()
                    .iter()
                    .filter(|condition| {
                        condition.phase == trust_vc_core::scalar_cast_capture::ScalarCastEncodingPhase::CheckedCondition
                            && condition.original_typed_root == expected
                            && condition.prepared_typed_root == expected
                    })
                    .collect::<Vec<_>>();
                if matching.is_empty() || matching.iter().any(|row| row.casts.is_empty()) {
                    return Err(format!(
                        "native cast site {}:{} has no exact same-run typed encoding",
                        site.block, site.instruction
                    ));
                }
            }
            Ok(NativeScalarCastBinding {
                original_bundle,
                original_module,
                request_id,
                function_id,
                obligation_id,
                certificate: certificate.clone(),
                typed_request: observation.request,
                sites,
                encoding: observation.encoding,
            })
        })();
        self.bindings.borrow_mut().push(binding);
    }
}

pub(crate) fn bounded_json(value: &impl Serialize) -> Result<Vec<u8>, String> {
    struct Output(Vec<u8>);
    impl std::io::Write for Output {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if bytes.len() > MAX_ORIGINAL_BYTES.saturating_sub(self.0.len()) {
                return Err(std::io::Error::other(
                    "original cast binding exceeds data bound",
                ));
            }
            self.0.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut out = Output(Vec::new());
    serde_json::to_writer(&mut out, value).map_err(|error| error.to_string())?;
    Ok(out.0)
}
