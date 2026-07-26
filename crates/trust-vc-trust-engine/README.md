# trust-vc-trust-engine

`trust-vc-trust-engine` is the first trust-vc-native adapter boundary for tRust
verifier integration. It deliberately does not depend on a local tRust checkout
or on a proc-macro test harness.

The crate owns a small, serializable request model:

- `TrustVerificationRequest` groups one or more verification units.
- `TrustContractBundle` is the typed contract proof-IR facade for tRust
  adapters. It accepts only typed `requires`/`ensures` clauses, validates that
  each unit carries a native contract frame, and lowers to a full-mode
  `TrustVerificationRequest`.
- `TrustTrustIrAdapterRequest` is the versioned JSON adapter facade for
  trust-types/TrustIr compiler integration. It carries typed VC kinds, source
  spans, `TrustExpr` predicates, and `TrustProofLineage` under
  `TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION`; unsupported compiler constructs are
  represented structurally and fail closed before solver entry.
- `TrustVerificationUnit` describes one function or proof boundary.
- `TrustNativeContext` carries typed TrustIr/Rust function signatures, datatype
  declarations, invariant metadata, ownership/borrow state, and the typed
  contract frame for `result` plus `old(...)` snapshots.
- `TrustVariable`, `TrustSort`, and `TrustObligation` carry verifier facts.
- `TrustBootstrapProvenance` records first-class source metadata for
  non-contract bootstrap facts, such as typed bool/fixed-int cast semantics and
  typed ADT constructor/discriminant facts.
- `TrustExpr` lowers to native `TrustVcExpr` for full verification, including
  typed arithmetic, casts, calls, and pre-state `old(...)` references.
- `TrustProofPolicy` lets tRust request replayable Alethe proof artifacts from
  TrustVc. Certificate-bearing policies require full verification mode and fail
  closed when a verified unit can only provide metadata. The release-admissible
  policy additionally requires strict proof acceptance, kernel verification,
  zero proof holes, and zero trusted solver steps.
- `TrustProofEvidence` reports the exact evidence profile, reasoning kind, and
  assurance level for each verified obligation, so typed contract-frame
  Requires/Ensures evidence is distinguishable from ownership/memory evidence
  and from compatibility-mode source-string evidence. Evidence for typed
  obligations also preserves the serializable `TrustExpr` payload for downstream
  shape checks. Verified evidence carries a stable `TrustEvidenceCacheKey`;
  the enclosing unit report carries `TrustEvidenceCacheStatus`, initially
  `miss` for fresh solver-produced evidence.
- `TrustVcTrustEngine::consume_native_trust_ir_bundle` consumes upstream
  `trust_ir::NativeVerificationBundle` values directly, selects typed
  `NativeVerificationRequest::TrustVc` entries, and imports their proof
  certificates without adapter-name strings. Imported native certificate
  evidence reports release admission separately from raw presence, rejecting
  pending/failed/trusted obligations and trusted certificate payloads for
  release-grade compiler gates.
- `TrustVerifier` is the stable internal trait tRust-facing adapters can
  implement or wrap. `TrustVcTrustEngine::validate_request`,
  `validate_trust_ir_adapter_request`, and `validate_native_trust_ir_bundle` expose
  solver-free validation for compiler integration probes.

`TrustVcTrustEngine` is the initial implementation. It lowers each unit into
`trust_vc_core::vc::VerificationContext` and calls
`VerificationContext::verify_with_report`, so callers can verify native
obligations and capture diagnostics without relying on thread-local proc-macro
collection.

The crate also ships `trust-vc-trust-runner`, a deterministic JSON CLI for
compiler integration tests and stage2 probes. The runner reads a serialized
`TrustVerificationRequest`, `TrustTrustIrAdapterRequest`, or
`trust_ir::NativeVerificationBundle` with `--input`, auto-detects the format by
default, optionally accepts
`--input-format trust-request|trust-ir-adapter|native-trust-ir-bundle`, optionally
overrides the request proof policy for Trust solver requests with
`--proof-policy`, and writes a serialized report with `--output`. Use
`--input -` or `--output -` for stdin/stdout integration. The TrustIr adapter path
calls `TrustVcTrustEngine::verify_trust_ir_adapter_request`, so unsupported
tRust/TrustIr constructs fail closed before solver entry. The MIR memory path
accepts a serialized `TrustMirMemoryProofUnit`, runs the facade's ownership
preflight, and returns the normal Trust verification report. The native TrustIr
bundle path calls `TrustVcTrustEngine::consume_native_trust_ir_bundle` and imports
typed TrustVc proof-certificate requests directly.

Decision for #2789/#2790: TrustVc now supports both Trust-owned typed request
facades and the upstream native TrustIr request bundle. tRust-owned trust-types
values can still lower into `TrustTrustIrAdapterRequest` or
`TrustVerificationRequest`, while producers that already hold native TrustIr can
hand TrustVc a `NativeVerificationBundle` with typed TrustVc request variants.
TrustVc validates full-mode Trust payloads before solver execution and validates
native TrustIr bundles before importing certificate evidence.

The checked-in `fixtures/trust_ir_adapter/` goldens are TrustVc-owned adapter
projections anchored to real tRust JSON goldens under
`crates/trust-integration-tests/tests/`. They cover the positive
`trust_fixture_x86_load` binary-to-TrustIr memory/provenance path and the
fail-closed unresolved-indirect-branch path. The #2789/#2790
`trust_increment_contract_cfg_trust_ir_adapter_golden.json` fixture is a native
tRust-produced `TrustTrustIrAdapterRequest` covering first-class requires/ensures
contract-frame evidence and typed CFG proof evidence without string-backed
adapter payloads.
The checked-in `fixtures/trust_ir_native/native_request_trust_bundle.json` fixture
is copied from TrustIr's conformance corpus and pins direct consumption of the
upstream `NativeVerificationBundle` TrustVc request variant. Native certificate
imports are report-only unless a consumer enforces release admission:
`admissible` means the TrustIr obligation is discharged and the certificate does
not rely on `ProofEvidence::Trusted`; `rejected` carries precise reasons such
as `obligation_pending`, `obligation_failed`, `obligation_trusted`, or
`certificate_uses_trusted_evidence`.

Native-readiness checks are fail-closed for obligations that would otherwise
overclaim verifier coverage. Translation-validation obligations require a typed
function signature, type-invariant obligations require invariant metadata,
memory-safety obligations require ownership/borrow state, typed ADT bootstrap
facts require datatype metadata, and typed `old(...)` references require a
contract-frame snapshot. Full mode rejects string-backed obligations before
solver execution, and non-contract bootstrap facts require first-class
provenance before full-mode lowering. Compatibility mode keeps accepting legacy
bootstrap payloads without provenance. Full verification returns per-obligation
proof evidence only after the unit verifies. Builds with the
`proof-certificates` feature can
attach replayable ay/Alethe proof payloads with stable SHA-256 artifact ids,
strict/kernel checker status, release-admission status, and explicit
assumption/assertion provenance.
Per-obligation proof evidence now carries native profiles for
`typed_contract_frame`, `ownership_memory`, typed cast/ADT bootstrap and
invariant lanes, and legacy compatibility evidence; downstream Trust
aggregators must consume those profiles instead of treating `Verified` as a
single proof-strength bit.
