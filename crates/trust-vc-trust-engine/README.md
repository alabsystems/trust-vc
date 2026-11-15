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
  pending/failed/trusted obligations, trusted certificate payloads, and
  certificates whose coverage trust-ir-build does not DERIVE as `Unbounded`
  from the kernel replay of that very certificate, for release-grade compiler
  gates (see "Release admission of native certificates" below).
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

TrustVc supports both Trust-owned typed request
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
fail-closed unresolved-indirect-branch path. The
`trust_increment_contract_cfg_trust_ir_adapter_golden.json` fixture is a native
tRust-produced `TrustTrustIrAdapterRequest` covering first-class requires/ensures
contract-frame evidence and typed CFG proof evidence without string-backed
adapter payloads.
The checked-in `fixtures/trust_ir_native/native_request_trust_bundle.json` fixture
is copied from TrustIr's conformance corpus and pins direct consumption of the
upstream `NativeVerificationBundle` TrustVc request variant.

**Release admission of native certificates.** Each imported certificate is
graded `admissible` or `rejected`, and the grade is enforced, not just
reported: a request with any rejected certificate folds to
`certificates_rejected`, which `validate_native_trust_ir_bundle` returns as
`Err(NativeTrustIrBundleVerdictNotClean)` and `trust-vc-trust-runner` exits
with **5** (only `certificates_admitted` exits 0). `admissible` means the
TrustIr obligation is `discharged` or `certified`, the certificate does not
rely on `ProofEvidence::Trusted`, and its COVERAGE is DERIVED as `Unbounded`
by this consumer from evidence it re-checks — never read from a
producer-written `ProofCertificate::assurance` row. The rule
(`src/native_coverage.rs`) calls trust-ir-build's
`coverage_establishment_report` with no attestation and no replayer, so only
**basis K** can establish: after `validate_upstream_bundle` and the identity
checks pass, (1) the report must be checked, (2) the certificate's OWN
verdict (`for_certificate` of its lineage reference) must be `Established {
bound: Unbounded, basis: KernelReplayedClaim }` naming that very certificate —
this process replayed it in the Clean kernel against the claim re-derived
from its obligation, and the claim's family (today only
`ContractGroundDecision`, a universally closed contract decision) is
`Unbounded` — (3) the report must record NO refusal anywhere in the
bundle, and (4) the certificate's obligation must state exactly ONE SMT-LIB
formula text: schema `smtlib2` (whose payload IS SMT-LIB source, as
trust-ir's own SMT-LIB2 reader decides it: one well-sorted quantifier-free
`Bool` term over the clause's own bindings,
`trust_ir::spec_surface::check_linked_invariant` — this crate keeps no byte
rules of its own), no `smtlib` rendering or one byte-equal to the payload, no
sort but `Bool`. trust-ir's own validator refuses a bundle that breaks the
schema, rendering or source clause (its contract grounder reads only
`ProofFormula::smtlib_text`, through the same SMT-LIB2 reader), but at the
pinned trust-ir the grounder ignores the sort, so without (4) a replay could
prove a formula of sort `Int`, which no SMT-LIB reader reads as a predicate. A
refusal means a producer stated something false (for example an in-module
row claiming more than its certificate's derived bound) and is fatal for
every certificate of the bundle; an undetermined verdict on some other
certificate blocks nothing. Basis R (a verified solver result cited by
a sealed attestation) is per OBLIGATION and vouches for no certificate, so
it never admits one; no basis-R input is accepted here. `certified` is
judged on its replay, not its label: it stands or falls with the same kernel
replay (an SMT or `Trusted` certificate on a `certified` obligation is
refused).
An `admissible` certificate also needs a published assertion id. A certificate
states its formula as ONE SMT-LIB text (its obligation's `formula`, read by
trust-ir's replay and by rule (4)) and its assertion id in its own field: the
`assertion_id` of the `Assertion` replay atom that the TrustVc request citing
it carries for its obligation (`provenance.replay_context`), which is the atom
Trust's `trust-ir-bridge` writes — the obligation's formula cloned, beside the
compiler-fact number. The request digest covers the atom's formula text, its
obligation and its id, and the row republishes that digest as
`request_digest`. The export seam (`src/native_assertion_id.rs`) refuses the
bundle when an atom's id differs from the compiler fact's, when an `Assertion`
atom's formula is not exactly its obligation's (bindings included: the digest
does not cover them), or when two atoms for one obligation disagree; it
publishes the id only when the citing request carries exactly one such atom
for the obligation and no other obligation in the bundle carries the number
(in a compiler fact, a payload or any request's replay atom). In effect a
number carried by two or more obligations publishes no id for any of them,
whatever formula or string they share: trust-ir refuses two compiler facts
with one public obligation id, so two obligations never count as one
assertion. That also withdraws the id from a legitimate assertion with several
obligations; it fails closed. An obligation also carries every number its
string (`source.assertion_id`, or the payload's) carries anywhere in the
bundle, so an unnumbered obligation that shares a numbered one's string
withdraws that number. A replay atom, or any other formula the module states
(a function summary's `requires`, `ensures` or `decreases` clause, a spec
invariant or temporal formula), that renders the number or its string and is
not exactly an obligation's own formula also withdraws it, and so does a
replay atom of any kind, in any request, that states the number as its own id
beside a formula other than its obligation's. The payload reader is strict:
each of the two payload schemas accepts exactly one shape, the one Trust's
`trust-ir-bridge` writes (a `trust-types.Formula@1` object with only `formula`
and `source`, the source record with only `source_id`, `assertion_id`,
`native_assertion_id` and `span`; under `trust.trust_ir.obligation-source.v1`
that record is the whole document, plus the producer's three marker strings),
every key optional, each value of one exact type, and the module docs of
`src/native_assertion_id.rs` write it down. A payload anywhere in the bundle,
in any of those places, that is not that shape (not JSON, a key repeated
inside one object, a document that is not an object, an identity key outside
the source record, a key the shape does not have, a value of the wrong type
such as a `native_assertion_id` of `"1"`, `1.0` or `4294967297`) is
unreadable: it might carry any number, so it withdraws every id in the bundle,
and beside a compiler-fact number it refuses the bundle. Otherwise the certificate
is refused `missing_assertion_id`. A caller-named id
(`admit_proof_artifact(id)`) goes through the same rule: only the id the row
licenses is accepted. An id rendered inside a JSON
payload licenses nothing (such a payload is no SMT-LIB text, so trust-ir never
replays its certificate); a payload that renders the id differently still
refuses the bundle. The residual: every check compares renderings inside one
bundle, so a consistent relabeling of the numbers is admitted under the new
numbers. That covers moving the compiler fact and the atom together to an
unused number (also a number deleted from an unrequested obligation's fact
and moved under a fresh string), and swapping the numbers of two obligations
(each certificate is then admitted under the other's old number). No field of the bundle can
refuse either (the IR carries no numeric assertion id, and neither the site,
the span nor the request's obligation list relates to one), so assertion
numbering is trusted to the producer. An admitted id names one obligation
within its own bundle; do not join it with numbers from another bundle or
producer run.
`rejected` carries precise reasons such as `obligation_pending`,
`obligation_failed`, `obligation_trusted`, `certificate_uses_trusted_evidence`,
`certificate_coverage_undetermined` (no kernel replay of this certificate,
an unclassified claim family, a kernel-less build, an unchecked report, or an
obligation that does not state exactly one SMT-LIB formula text),
`certificate_coverage_basis_not_this_certificate` (a SIBLING certificate on
the same obligation was replayed, not this one), `certificate_coverage_bounded`,
or `certificate_coverage_refused` (the admission's `coverage_detail` carries
trust-ir-build's own words); an established admission names its
`coverage_basis` (the replayed certificate and its claim family). The retired
row-judging labels (`certificate_coverage_unrecorded`, `_request_unknown`,
`_obligation_not_requested`, `_bound_mismatch`, `_contested`,
`_not_established_for_module`) are no longer produced and decode as
`certificate_coverage_not_judged`. The same coverage refusals travel onto the
`TrustVcNativeProofArtifact` built by `admit_native_proof_artifact(s)`, so a
certificate refused for coverage never yields an `accepted` artifact; an
artifact built with no coverage judgement at all (by hand, or from a payload
that predates it) is rejected `certificate_coverage_not_judged`. **The wire
is not evidence:** coverage is judged only against the bundle a certificate cites, which no serialized
admission, evidence item, report or proof artifact carries. Decoding any of
them therefore re-derives what its own fields support and never reads the
verdict it states — a decoded certificate admission is `rejected` (its
coverage `certificate_coverage_not_judged` unless the payload names a
coverage refusal), a certificate-mode request report declaring
`certificates_admitted` is refused, and a proof artifact
is rebuilt from its binding (admission and fingerprint recomputed, coverage
not judged). A request report names the obligations its request names
(`obligations`, required on the wire), and `certificates_admitted` is the fold
"every named obligation is answered by admissible evidence and nothing else
is" — never vacuously true. A discharge-mode report DECODES AS `not_judged`, every
outcome `not_judged`, whatever it declares: its outcomes are labels the wire
carries no evidence for (witness bindings stay in process), so decoding reads
none of them. The erasure belongs to `TrustVcNativeTrustIrDischargeObligation`
itself, so it holds on EVERY decode path — a report, a bundle, and a
standalone `TrustVcNativeTrustIrDischargeAnswer` or obligation. A payload no
producer writes is still refused — a discharge report wearing a certificate
verdict, an answer that does not answer each named obligation exactly once, a
named list that repeats an id (`[0, 0]`). A verdict for a decoded report
comes back only through
`TrustVcTrustEngine::rejudge_native_trust_ir_discharge_report(module, request,
report)`, which refuses a report not bound to that request and module (request
id, request and module digests, function, and EXACTLY the request's obligation
list — a consistently renamed id such as `0 -> 4242` is refused) and then
discharges the request afresh. A decoded bundle's rollup is the fold of its
decoded requests. The artifact fingerprint binds the
obligation status, the trusted flag and the coverage judgement including its
BASIS (the kernel-replayed certificate and claim family), and
`TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION` is 8: a v7 artifact (whose
fingerprint bound a judgement of the retired row rule) or a v6 one is
refused as stale. An import whose obligation carries a
temporal-property attribution (`ProofObligation::spec`) or a kind the report
has no faithful label for (temporal safety, liveness, termination, ownership,
give-back refinement, a custom kind) is refused outright, never filed as
`panic_freedom`.

Producers mint `assurance: None` (the driver seam `trust-vc-driver`
`compiler_facts::certificate_to_trust_ir`, the trust-ir corpus bundle, Trust's
trust-ir bridge), and that is right: coverage is the consumer's derivation, and
a `Some` row is non-authoritative and refused when it over-states its
certificate's derived bound. The corpus certificate verbatim, `Certified`
with no row, has its coverage established and is refused only for its missing
assertion id (upstream's TrustVc request carries no replay atom); with the
atom the bridge writes it is release grade (`tests/native_coverage_basis_k.rs`).

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
Per-obligation proof evidence carries native profiles for
`typed_contract_frame`, `ownership_memory`, typed cast/ADT bootstrap and
invariant lanes, and legacy compatibility evidence; downstream Trust
aggregators must consume those profiles instead of treating `Verified` as a
single proof-strength bit.
