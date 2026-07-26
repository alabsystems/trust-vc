# Design: trust-vc as Trust's proof backend — a better Verus, backed by ay

> **North star (2026-06-14).** trust-vc is a **submodule of Trust**
> (`first-party/trust-vc` in the Trust superproject) and its ultimate role is
> **Trust's proof-calculus + SMT backend**. Being a drop-in replacement for Verus
> remains a hard goal — it is how we *benchmark and gate* parity (`cargo trust-vc
> evidence`) — but it is the *milestone*, not the *destination*. The destination
> is: Trust's compiler feeds trust-vc fully type-/borrow-checked facts, trust-vc
> lowers them to its own typed IR and discharges them with **ay**, and every
> "Verified" comes with an **independently checkable proof certificate** that
> Verus's black-box Z3 cannot produce. This document is the authoritative design;
> `design-rustc-driver-frontend.md` is now the *Verus-compatibility front end*
> (one of two front ends) under it.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

---

## 1. Identity and dual mandate

trust-vc has **two** consumers, served by **one** back end:

1. **Inside Trust (the product).** Trust is a rustc fork
   with an in-tree MIR verifier (`compiler/rustc_mir_transform/src/trust_verify.rs`)
   and a unified verification story (model checking = trust-mc, separation logic =
   trust-wp, proof calculus = **trust-vc**). trust-vc is the **proof-calculus and
   SMT-discharge engine** of that single verifier. Per
   `TRUST_NATIVE_VERIFIER_V2.md`: tRustc owns `requires`/`ensures` syntax, contract
   typing, the `TrustContractBundle`, and cross-crate metadata; **trust-vc owns
   ghost code, lemmas, `assert_by`, triggers, `decreases`/termination, refinement
   /type invariants, and proof summaries + certificates.**

2. **Standalone, as a Verus replacement (the benchmark).** trust-vc also runs as a
   self-contained verifier over the upstream Verus corpus, which is how parity is
   measured and gated. This keeps trust-vc honest and portable, and is the proving
   ground for the proof language.

The same `TrustVcExpr` IR → encoder → ay → `trust-vc-kernel` certificate pipeline
serves both. Only the **front end** differs (see §4).

---

## 2. The integration boundary already exists

This is not greenfield. The Trust↔trust-vc seam is built and versioned:

- **`trust-vc-trust-engine`** — the adapter boundary. Callers build a
  `TrustVerificationRequest` (or hand it a `trust_ir` bundle) and it lowers each
  unit into `trust_vc_core::vc::VerificationContext` and runs the existing solver
  pipeline (`src/lib.rs`).
- **`native_trust_ir_bundle.rs`** — a *direct* consumer of upstream
  **`trust_ir::NativeVerificationBundle`** (`NativeVerificationRequest::TrustVc`).
  It already speaks the types that matter:
  - **`NativeCompilerFactRef`** — the compiler's resolved facts (types, borrow/
    region info). *This is precisely the information the syn front end cannot get*
    (see `design-rustc-driver-frontend.md` §2). In-Trust, Trust's compiler
    hands it over; no reconstruction, no `rustc_private` driver.
  - **`ProofCertificate` / `ProofCertificateRef` / `ProofEvidence` /
    `ProofLineageNode`** — the certificate + provenance trust-vc emits back.
  - `SourceSpan`, `TrustVcVerificationMode`, `ProofObligation`, `ProofStatus`.
- **`trust_ir_adapter.rs`** — a versioned, serializable JSON boundary so trust-vc
  "avoids a direct dependency on still-moving compiler crates" while Trust
  integration stabilizes.
- **`trust-vc-merge-contract`** — `MergeBundle` v4 (`FuncDeclMeta`, `FuelAxiomMeta`,
  `BroadcastLemmaMeta`, `SortMeta`) — the versioned handoff contract.
- **`mir_memory.rs`** — a MIR memory model for exec/borrow reasoning.

So the design is: **finish and lean into this boundary**, not invent a new one.

---

## 3. Architecture

```
  Trust superproject (rustc fork)
  ┌──────────────────────────────────────────────────────────────────────────┐
  │  trustc  (HIR → THIR → MIR, full typeck/trait-res/borrowck)               │
  │     │                                                                      │
  │     │  trust_verify MIR pass + contract lowering                          │
  │     ▼                                                                      │
  │  trust_ir::NativeVerificationBundle                                        │
  │     • NativeCompilerFactRef   ◀── resolved types / borrows / regions       │
  │     • ProofObligation(s)      ◀── requires/ensures/asserts/decreases       │
  │     • TrustContractBundle     ◀── typed contracts (tRustc-owned)           │
  └─────────────────────────────────┬────────────────────────────────────────┘
                                     │  (stable trust-ir JSON boundary)
  ┌──────────────────────────────────▼───────────────────────────────────────┐
  │  first-party/trust-vc  (this submodule)                                    │
  │                                                                            │
  │   trust-vc-trust-engine :: native_trust_ir_bundle / trust_ir_adapter       │
  │            │  lower compiler facts + obligations                           │
  │            ▼                                                               │
  │      TrustVcExpr / TrustVcType  (own typed IR — syn-free at the surface)   │
  │            ▼  VerificationContext                                          │
  │      encoder  →  ay (pure-Rust SMT; native Seq/Set/Map/String/FP/BV)       │
  │            ▼                                                               │
  │      VerifyResult  +  ay UNSAT proof                                        │
  │            ▼                                                               │
  │      trust-vc-kernel  → checks the certificate independently               │
  │            ▼                                                               │
  │      trust_ir::ProofCertificate / ProofEvidence / ProofLineageNode  ───────┼──▶ back to Trust
  └────────────────────────────────────────────────────────────────────────────┘

           Parity gate (benchmark): cargo trust-vc evidence over the Verus corpus
```

**Front-half (per §4) is the only thing that varies; the back-half — IR, encoder,
ay, kernel — is shared by both the in-Trust and the standalone paths.**

---

## 4. Two front ends, one back end

| | **Primary: in-Trust** | **Compat: standalone** |
|---|---|---|
| Source of types/borrows | Trust compiler facts via `trust_ir::NativeCompilerFactRef` | rustc-driver THIR (`trust-vc-driver`, nightly) **or** the legacy `syn` reader |
| Front-end crate | `trust-vc-trust-engine` (exists) | `trust-vc-driver` (skeleton) / `ir_lowering` (legacy) |
| `rustc_private` nightly pin | **not needed** — Trust *is* the compiler; trust-vc consumes a stable trust-ir boundary | needed only for the standalone driver |
| Purpose | the product: Trust's proof backend | the benchmark: Verus drop-in parity + non-Trust use |
| Information ceiling | **gone** (compiler hands over facts) | closed by the driver; open under legacy syn |

The standalone rustc-driver (`design-rustc-driver-frontend.md`) is retained
because it powers the **Verus-parity benchmark** and lets trust-vc verify
vanilla-rustc/Verus code *outside* Trust. But the cost that dominated that
design — the external `rustc_private` toolchain pin — **does not apply to the
product path**, because in-Trust the compiler facts arrive over the trust-ir
boundary that already exists.

---

## 5. Why this is *a better Verus*, backed by ay

Concrete, defensible advantages — each rooted in code that exists or in ay
capabilities trust-vc owns:

1. **Independently checkable proof certificates (the headline).** ay emits UNSAT
   proofs; `trust-vc-kernel` checks them; the result is carried as
   `trust_ir::ProofCertificate`/`ProofEvidence`/`ProofLineageNode`. **Verus trusts
   Z3 as an unaudited oracle** — a "Verified" is only as trustworthy as Z3. In
   Trust, a "Verified" is *certificate-checked by a small, separate kernel*. This
   is a soundness property Verus structurally cannot match, and trust-ir already
   models the certificate lineage end to end.
2. **One verifier across all levels.** Trust reasons about MIR/exec + borrows
   (`trust_verify`, `mir_memory`), model checking (trust-mc), separation logic
   (trust-wp), **and** the proof calculus (trust-vc) — over **one** IR family and
   **one** solver (ay). Verus is Rust-surface-only and Z3-only. A bug found by one
   level cross-validates the others.
3. **The information ceiling is dissolved at the source.** The reason 100% Verus
   parity is hard (the syn front end can't see types/traits/borrows; see the
   companion doc) **does not exist on the product path**: Trust's compiler emits
   `NativeCompilerFactRef`. trust-vc lowers facts, it does not reconstruct them.
4. **Owned, pure-Rust solver that sidesteps Z3's limits.** ay has native decision
   procedures for Seq/Set/Map/Multiset/String/FP/BV, turning the quantifier-heavy
   surface (where Verus must lean on Z3's MBQI/e-matching) into *decidable*
   territory — and because we **own** ay, every completeness gap is a fixable,
   measurable target (the differential oracle), not a black box.
5. **No Z3, no external SMT.** Reproducible, dependency-clean (ay's TCB is
   GMP/MPFR/libc + a self-hosted JIT), and shippable inside the Trust toolchain.
6. **Cross-IR portability + differential oracle.** Because trust-vc consumes the
   universal `trust-ir`, it can verify Trust MIR *and* Verus-surface programs under
   one engine, and run ay-vs-Z3 differentially on identical SMT — a portability and
   cross-checking claim beyond Verus's Rust-only, Z3-only scope.

**The crisp statement of "better":** *Verus proves Rust with Z3 you must trust;
Trust+trust-vc proves Rust — and MIR, and protocols — with ay you can check.*

---

## 5a. Superiority capability roadmap (ranked by impact / effort)

Concrete features that turn "backed by ay + trust-ir" into a decisive edge. Each
exploits something Verus's Rust-surface + black-box-Z3 stack structurally cannot.
Ranked by impact/effort. **All seven now have a first, tested increment** — see
the Built table below and §9.

| # | Capability | What | Why Verus can't | I/E |
|---|-----------|------|-----------------|-----|
| **1** ✅ | **Kernel-checkable VC certificates** | Emit an ay UNSAT/Alethe proof per VC, re-checked by `trust-vc-kernel`; carry it in the `trust_ir::ProofCertificate` lineage. | Z3 is a black box; a Verus "Verified" has no checkable artifact. | H/M |
| **2** ✅ | **Compiler-fact frame/alias VCs** | Generate VCs from `trust-ir`'s resolved borrow/alias/region facts, proving frame conditions from *actual* Rust ownership, not surface specs. | Verus reasons from Rust-surface specs, not compiler-resolved borrow lineage. | H/M |
| **3** ✅ | **Certified cross-crate proof cache** | Cache kernel-checked certificates keyed by a content hash of the IR; a cache hit replays the checkable cert instead of re-proving. | Z3 proofs aren't stable, checkable artifacts tied to compiler IR, so they can't be safely cached/replayed. | H/L |
| **4** ✅ | **Native collection decision procedures** | First-class finite `Seq/Set/Map/Multiset` reasoning for `Vec`/slices/maps — membership, length, bag-count — with no quantifier blowup. | Verus leans on Z3 array+quantifier encodings and MBQI fragility. | H/M |
| **5** ✅ | **Exact string/byte proofs** | `String`/`str` as `Seq<char>` + `BV` reasoning (length, char-at, bounds). | Z3 string/sequence support is incomplete/heuristic under Verus's encodings. | M/M |
| **6** ✅ | **Bit-precise unsafe/layout contracts** | Prove size/align/niche/offset invariants via `BV`/integer reasoning from layout facts. | Verus does not take rustc-derived layout/provenance as proof inputs. | H/H |
| **7** ✅ | **Specialization dispatch (ay-JIT hook)** | Fingerprint a VC's structural shape and key a solver strategy on it — the trust-vc side of ay's self-hosted JIT specialization. | Verus cannot specialize or improve Z3's internals while keeping checkable proofs. | M/M |

(Capabilities 1–7 sourced from an external `codex` design review, 2026-06-14,
filtered against the codebase, then built as feature-gated increments.)

### Built (2026-06-14) — `crates/trust-vc-driver`, feature-gated, default build / gate undisturbed

| # | Module | Feature | Tests | Leverages (Verus/Z3 cannot) |
|---|--------|---------|------:|-----------------------------|
| 1 | `lower::verify_certified` | `certificates` | 2 | ay UNSAT/Alethe proof, kernel-checked (`kernel_verified==true`) |
| 2 | `compiler_facts` | `trust-integration` | 4 | `trust-ir` compiler facts → frame VCs (unmodified ⇒ unchanged) |
| 3 | `cache` | `cache` | 2 | replay a kernel-checked certificate without re-proving |
| 4 | `collections` | `collections` | 8 | ay-native Seq/Set/Map/Multiset (ground array+arith, no MBQI) |
| 5 | `strings` | `strings` | 6 | `String`/`str` as `Seq<char>` + `BV` |
| 6 | `layout` | `layout` | 8 | size/align/offset invariants via `BV` |
| 7 | `tactics` | `tactics` | 6 | VC-shape fingerprint → ay-JIT dispatch |

All green together: `targo test -p trust-vc-driver --features all-capabilities`
(**59 tests, 0 failed**). Every capability is **fail-closed**: where a symbolic
property hits solver incompleteness it returns `Unknown` (never a false
`Verified`) — e.g. some symbolic set-disequality directions in #4 are `Unknown`,
asserted as such, not refuted. #7's actual native-code specialization is ay-side;
the module is the trust-vc dispatch hook that selects/feeds it.

## 6. What exists vs what's needed

**Exists:** the trust-ir bundle consumer (`native_trust_ir_bundle.rs`), the
versioned adapter (`trust_ir_adapter.rs`), the MergeBundle v4 contract, the typed
IR/encoder/ay/kernel back half, the certificate types in trust-ir, and the
evidence gate (parity benchmark).

**Needed (dependency-ordered):**
1. **Compiler-fact lowering completeness** — map the full `NativeCompilerFactRef`
   surface (generics/substitutions, associated types, borrow/region facts,
   const-eval) into `TrustVcExpr`/`TrustVcType`. This is the in-Trust analogue of
   the driver's THIR lowering and is where the parity clusters unlock as
   *categories*.
2. **Certificate round-trip hardening** — close the `trust-vc-kernel` BV/Array/Seq
   certificate gap (grand-strategy §5) so *every* in-Trust "Verified" is
   independently checkable, not just the fragment the kernel covers today.
3. **Gate wiring for the typed path** — bridge typed obligations to the evidence
   gate's `sha256(condition-string)` fingerprints (see companion doc §R5) so the
   in-Trust path can be parity-gated, not only the legacy syn path.
4. **ay Problem-B program (parallel, front-end-independent)** — native-theory
   completeness for symbolic collections, MBQI counterexample finding, nonlinear
   (Gröbner/CAD). A perfect front end still emits VCs ay must discharge; this is
   the differential-oracle + native-theory track from `grand-strategy-ay.md`.

---

## 7. Honest bounds

- **The Trust path does not bypass Problem B.** Better/typed inputs do not make ay
  more complete; the symbolic-collection/quantifier/nonlinear residue still needs
  solver work. The certificate edge is also bounded by kernel completeness (item 6.2).
- **Parity gate independence is preserved.** The Verus-parity verdict still
  measures trust-vc's *own* corpus run; the Trust integration is the deployment of
  the same engine, not a redefinition of the benchmark.
- **This is not Path 2.** trust-vc consumes Trust's *own* compiler IR (and, in
  compat mode, raw rustc THIR) — never Verus's VIR/AIR. Independence is *from
  Verus*; depending on Trust's compiler is the whole point of being Trust's backend.

---

## 8. Relationship to the other design docs

- `design-rustc-driver-frontend.md` — the **Verus-compatibility front end**
  (standalone rustc-driver) under this north star; its `lower.rs` seam is shared
  with the in-Trust path.
- the internal grand-strategy-ay notes — the **Problem-B** program (differential oracle +
  native theories); composes with this design (item 6.4).
- `TRUST_NATIVE_VERIFIER_V2.md` — the ownership boundary between tRustc and
  trust-vc; this design realizes it.
- the internal Verus-replacement plan / parity-to-100 program notes — the parity
  benchmark program (item 6, gate).

---

## 9. Landed increments (2026-06-14)

In `crates/trust-vc-driver` (workspace member; non-default features OFF, so the
gated stable build and evidence gate are undisturbed):

- **The shared `lower` seam** (`src/lower.rs`, stable) — a fully-typed `DriverFn`
  (typed params, `requires`, symbolic `body_value`, `ensures`) → `Verification
  Context` → existing encoder + ay. `tests/lower_end_to_end.rs` proves it sound
  through real ay: valid postconditions → Verified, false ones → Refuted with a
  counterexample. This is the seam both front ends (in-Trust and standalone) share.
- **Capability #1 — kernel-checkable certificates** (`feature = "certificates"`,
  stable) — `DriverFn::verify_certified()` runs `verify_with_report`, extracts the
  ay UNSAT proof, and surfaces a `Certificate { kernel_verified, strict_verified,
  alethe, … }`. `tests/certificates.rs` proves the edge concretely: a verified
  function yields a certificate with **`kernel_verified == true`** (trust-vc-kernel
  independently re-checked a ~350-char Alethe proof); a refuted goal carries none.
  *This is the soundness property Verus's black-box Z3 cannot provide, now realized
  at the front-end seam.*
- **The standalone rustc-driver skeleton** (`feature = "rustc-driver"`, nightly) —
  the Verus-compat front end (`src/driver.rs`): `Callbacks::after_analysis(tcx)` →
  type-checked signature → `DriverFn`; fail-closed until THIR body/contract
  lowering lands.
- **Superiority capabilities #2–#7** — `src/{compiler_facts,cache,collections,
  strings,layout,tactics}.rs`, each feature-gated with its own test suite (see the
  Built table in §5a). All seven verify together via `targo test -p
  trust-vc-driver --features all-capabilities` (**59 tests, 0 failed**), default
  build clean, fmt + clippy clean.

These are honest **first increments**, not finished features: they prove each
capability end-to-end through the real ay backend, fail-closed on solver
incompleteness. The deepening work ahead — promote each from demonstrator to
general (e.g. #2 consume the full `NativeCompilerFactRef` surface and the real
`trust_ir` bundle, #3 round-trip the cached cert through `trust-vc-kernel` across
crate boundaries keyed by the monomorphized `trust-ir` hash, #4/#5 the symbolic
directions that still hit `Unknown`, #7 wire the dispatch into ay's JIT) — is the
ongoing program toward the goal: a 100% and strictly superior Verus replacement
that fully leverages ay, inside Trust.
