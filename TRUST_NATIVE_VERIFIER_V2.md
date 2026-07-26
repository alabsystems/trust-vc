# TrustVc in Trust Native Verifier V2

Date: 2026-04-25
Status: alignment directive

> North star: [`design-trust-proof-backend.md`](design-trust-proof-backend.md)
> — trust-vc is a submodule of Trust whose ultimate role is Trust's
> proof-calculus + SMT backend (on the pure-Rust ay solver, no Z3).

## Principle

TrustVc is the proof-calculus capability inside the single Trust verifier. It is
not a second Trust contract frontend.

tRustc owns:

- `#[requires]` and `#[ensures]` syntax;
- contract typing;
- `TrustContractBundle`;
- cross-crate metadata;
- release proof policy.

TrustVc owns:

- ghost code;
- lemmas;
- `AssertBy`;
- triggers;
- decreases and termination arguments;
- refinement/type invariants;
- proof summaries and certificates.

## Required Native Boundary

TrustVc must consume Trust's compiler IR — **`trust-ir`** (resolved compiler
facts: types/borrows, via `trust_ir::NativeCompilerFactRef`) — and typed contract
bundles directly, through the `trust-vc-trust-engine` adapter. The normal Trust
path must not rely on macro/thread-local collection or a parallel plain-contract
parser.

TrustVc evidence must include:

- stable obligation ID;
- proof summary/certificate provenance;
- dependencies and reusable assumptions;
- source spans and diagnostics;
- explicit unsupported reasons for proof features not yet implemented.

## Current Next Steps

1. Keep typed native request preparation and call-site `Ensures`-as-assumption
   semantics.
2. Lower `TrustContractBundle` and Trust proof IR into TrustVc native requests.
3. Implement native `AssertBy`, triggers, loop metadata, type/trait metadata,
   decreases, and proof certificates.
4. Make summaries reusable by TrustWp/TrustMc only when tRustc records explicit
   TrustVc provenance.

TrustVc makes hard contracts tractable. It does not own the public Trust
contract language.
