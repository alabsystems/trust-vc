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
> `docs/archive/design-rustc-driver-frontend.md` is now the *Verus-compatibility front end*
> (one of two front ends) under it.

> **Update 2026-09-17 — read with the sections below.**
>
> - **What "done" means (owner direction, 2026-09-17).** The Trust toolchain
>   does not discharge proof obligations on ay directly: it discharges them
>   through the trust-vc engine, which is being built out with Verus's
>   capabilities, and trust-vc discharges them on ay. Verus's capability list
>   is the checklist that says the full universe of options is supported, so
>   completion means every Verus verification capability at "full or superior"
>   power. The `cargo trust-vc evidence` verdict named above stays the corpus
>   instrument; it is a diagnostic, not the finish line. Measured 2026-09-17
>   on the project's internal capability checklist: 60 of 219 rows full or
>   superior (54 full, 6 superior), 105 partial, 50 missing, 4 not applicable.
>   Verus's concurrency capabilities are in trust-vc's scope as of the same
>   date.
> - **Seam status.** trust-ir has had a `DischargeProofObligations` request
>   mode since 2026-07-29, but `native_trust_ir_bundle.rs` answers it with
>   `DischargeNotAnswerable`: nothing in `trust-vc-trust-engine` lowers a
>   trust-ir function body yet. Importing and merging existing certificates
>   is wired, and trust-vc's own `TrustVerificationRequest` path (§2) lowers
>   and solves. Item 6.1 below is therefore the critical path for the
>   owner's definition of done.
> - **Duties from Trust's v6 rulings (2026-07-26).** Ruling D3 gives trust-vc
>   two jobs it does not do yet: own `Refinement` obligations, and act as the
>   deductive fallback for all five contract kinds. When that was recorded,
>   Trust's verifier had no fallback mechanism, so one has to be built. Ruling
>   D2 assigns automatic data-race obligations (`DataRace`,
>   `InsufficientOrdering`) to ty.
> - **Native theories are opt-in.** ay's native `Seq` and `String` sorts are
>   wired behind the `native-seq` / `native-strings` features of
>   `trust-vc-core`, both off by default; the default encodings are arrays.
>   The §3 diagram lists what ay supports, not what the default build uses.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

---

## 1. Identity and dual mandate

trust-vc has **two** consumers, served by **one** back end:

1. **Inside Trust (the product).** Trust is a rustc fork
   with an in-tree MIR verifier (`compiler/rustc_mir_transform/src/trust_verify.rs`)
   and a unified verification story (model checking = trust-mc, separation logic =
   trust-wp, proof calculus = **trust-vc**). trust-vc is the **proof-calculus and
   SMT-discharge engine** of that single verifier. Per
   `docs/archive/TRUST_NATIVE_VERIFIER_V2.md`: tRustc owns `requires`/`ensures` syntax, contract
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
  pipeline (`src/lib.rs`). *(2026-09-17: that lowering covers trust-vc's own
  request type; a `trust_ir` bundle in `DischargeProofObligations` mode is not
  yet answerable — see the update block at the top.)*
- **`native_trust_ir_bundle.rs`** — a *direct* consumer of upstream
  **`trust_ir::NativeVerificationBundle`** (`NativeVerificationRequest::TrustVc`).
  It already speaks the types that matter:
  - **`NativeCompilerFactRef`** — the compiler's resolved facts (types, borrow/
    region info). *This is precisely the information the syn front end cannot get*
    (see `docs/archive/design-rustc-driver-frontend.md` §2). In-Trust, Trust's compiler
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
  │      trust-vc-kernel  → re-checks the certificate (resolution + EUF/LRA;   │
  │                          NIA/BV/Array/Seq accepted on trust)               │
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
| Source of types/borrows | Trust compiler facts via `trust_ir::NativeCompilerFactRef` | rustc-driver THIR (`trust-vc-driver`, Trust toolchain `rustc_private`) **or** the legacy `syn` reader |
| Front-end crate | `trust-vc-trust-engine` (exists) | `trust-vc-driver` (skeleton) / `ir_lowering` (legacy) |
| `rustc_private` | **not needed** — Trust *is* the compiler; trust-vc consumes a stable trust-ir boundary | needed only for the standalone driver (served by the Trust sysroot) |
| Purpose | the product: Trust's proof backend | the benchmark: Verus drop-in parity + non-Trust use |
| Information ceiling | **gone** (compiler hands over facts) | closed by the driver; open under legacy syn |

The standalone rustc-driver (`docs/archive/design-rustc-driver-frontend.md`) is retained
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
   **Scope this honestly, today:** the kernel checks propositional resolution
   plus structural EUF (transitivity/congruence) and LRA (Farkas) lemmas, and
   returns `Trusted` for **NIA, BV, Array and Seq**
   (`crates/trust-vc-kernel/src/lib.rs:17`, `theory_check/mod.rs:44`) — the
   theories the machine-integer and collection encodings lean on hardest. Alethe
   is one of the kernel's *export* formats, not an input it re-checks. Closing
   that gap is item 6.2 below; until it closes, the headline is a structural
   advantage over Verus, not a delivered end-to-end guarantee.
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
5. **No Z3, no external SMT.** Reproducible, dependency-clean (ay's native TCB
   is `libc` for resource limits plus `ay-jit`, its self-hosted JIT; GMP/MPFR via
   `rug` are gone — they left `Cargo.lock` at `9d3f8fc5` and arbitrary precision
   is now `num-bigint`), and shippable inside the Trust toolchain.
6. **Cross-IR portability + differential cross-checking.** Because trust-vc
   consumes the universal `trust-ir`, it can verify Trust MIR *and* Verus-surface
   programs under one engine, and the same SMT can be run ay-vs-Z3 differentially
   — a portability and cross-checking claim beyond Verus's Rust-only, Z3-only
   scope. The oracle that does that differential now lives in **ay**, as its
   `ay-z3-parity classify` subcommand; it was extracted out of trust-vc at R1 and
   is no longer a deliverable of this repo.

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
(**59 tests, 0 failed**; measured 2026-06-14 with that spelling — today `targo`
requires an explicit lane, e.g. `targo --unverified test -p trust-vc-driver
--features all-capabilities`, and the count was not re-run for the 2026-09-17
update). **Re-run 2026-09-23 (not all green):** at trust-ir `4f09dab8` the gate
did not compile (E0063, `ProofCertificate::assurance` missing in
`compiler_facts::certificate_to_trust_ir`; fixed with `assurance: None`, i.e.
coverage NOT RECORDED). Compiled, with `--no-fail-fast`: **66 tests, 65 passed,
1 failed** — `strings::shorter_string_has_smaller_len_verifies` comes back
`Unknown` (`SolverPanic`: "sort mismatch in bvslt: expected BitVec(w),
BitVec(w), got Int, Int" from the overflow pre-pass), fail-closed, not a false
`Verified`. Neither trust-vc-core nor the driver's `strings` capability changed
between `79cda0ad` (the last commit where the gate compiled) and this re-run;
whether it was red there was not measured. **Closed 2026-09-24 (green):** the
red was an encoding inconsistency, not a strings bug. Spec-collection lengths
are unbounded non-negative `Int` terms (Route A, #2779), but the driver types
the string-length view `Int { width: 64 }`, so `a.len() < b.len()` had two
explicit-BV IR types and two `Int` terms and fell through to `bvslt`.
`encode_compare` (trust-vc-core `arith/compare.rs`) now decides by the TERM
sort: an `Int`-sorted operand makes it an integer comparison
(`try_encode_int_sorted_compare`), including on the #2557 BV-compare branch.
The same edit fixes a false `Verified` on that boundary, measured at HEAD's
`compare.rs`: the Route A lift of a BV peer was unconditionally unsigned, so
`a.len() == 2` entailed `a.len() < -1i64` (a negative `i64` read as
2^64 - 1); the lift now uses the peer's signedness. New pins in
`tests/strings.rs`: `longer_string_is_not_shorter_refuted` (the false twin of
the red) and `length_below_a_negative_bound_is_not_verified`. Measured
(`targo --unverified test -p trust-vc-driver --features all-capabilities
--no-fail-fast`, toolchain 321aaeda7, `../ay` at f399eca07): **68 tests, 0
failed** (strings 8/8).
**Reopened and re-closed 2026-09-24: signedness is the OPERAND's.** That
lift took the peer's sign from `term_widths`, a table keyed by TERM. ay
hash-conses constants, so `u64::MAX` and the `i64` literal `-1` are one term:
`u64::MAX < a.len() + (-1i64)` (with `a.len() == 0`) read its left operand as
`-1` after the right operand's `-1` re-registered the shared term, and came
back `Verified`; likewise `200u8 < a.len() + (-56i8)` and
`255u8 < a.len() + (-1i8)`. The arithmetic boundary (`bv_arith.rs`) still
lifted a signed peer of a length UNSIGNED: `a.len() + (-3) > 100` verified for
`a.len() == 2`, and the true `a.len() + (-3) < 0` was refuted. Every lift,
widening and ordering in the comparison, arithmetic, bitwise, shift, wrapping,
ITE, match, NOT/negation and `===` encoders now takes the signedness of the
operand's own IR type at the use site (`width_coercion::ir_type_signedness`);
a mixed signed/unsigned BV pair is compared as the integers it denotes; the
`term_widths` table answers a sign only while every registration of the term
agreed (`encoder/term_widths.rs`). A property check
(`trust-vc-core/tests/operand_signedness_proptest.rs`, i128 oracle, every
width, both signs) found three more of the class, each pinned in
`tests/operand_signedness_soundness.rs`. Driver pins: seven new cases in
`tests/strings.rs`, each in `verify` and `verify_exec`.

**Coverage at this seam — derived by the consumer, never recorded here.**
`compiler_facts::certificate_to_trust_ir` mints `ProofCertificate::assurance:
None`, which is right: the in-module row is non-authoritative, and trust-vc's
release admission DERIVES coverage from evidence it re-checks —
trust-ir-build's `coverage_establishment_report`, basis K, the Clean-kernel
replay of the very certificate (see `crates/trust-vc-trust-engine/README.md`,
"Release admission of native certificates"). This seam emits
`ProofEvidence::SmtProof` (Alethe), which no kernel replays, so its
certificates are still refused release admission —
`certificate_coverage_undetermined`, or
`certificate_coverage_basis_not_this_certificate` beside a replayed CleanCic
sibling — until they carry a kernel-replayable term of a classified claim
family. Citing a request (a CHC run, a TrustVc request) no longer
establishes anything.

Every capability is **fail-closed**: where a symbolic
property hits solver incompleteness it returns `Unknown` (never a false
`Verified`) — e.g. some symbolic set-disequality directions in #4 are `Unknown`,
asserted as such, not refuted. #7's actual native-code specialization is ay-side;
the module is the trust-vc dispatch hook that selects/feeds it.

## 5b. Integer semantics (decided 2026-09-24)

One rule set, applied by both frontends (the syn lowering and the typed
`VerificationContext::from_typed_parts` seam) and by the encoder, which does
not trust a producer's `ty` field where it disagrees with the operands.
Implemented in `trust-vc-core/src/ir_lowering/types.rs`
(`infer_expr_type`, `derive_binary_int_type`, `untyped_literal_value`) and
checked by `tests/integer_typing_proptest.rs` (i128 oracle) and
`tests/integer_typing_soundness.rs` (pins).

1. **The type of an arithmetic (`+ - * / %`), bitwise (`& | ^`) or
   conditional result is DERIVED from both operands** — never copied from
   the left operand, the then-branch, or a producer's declared type:
   * both operands of one fixed-width type `T` → `T`. This is trust-vc's
     machine integer model (`crates/trust-vc/examples/README.md`, "Integer
     model"): two's complement in `T`, and an exec `assert` whose arithmetic
     leaves `T` is refuted (`assertion::arithmetic_overflow_checked_for`).
     Spec obligations (`requires`/`ensures`/calc steps/call-site
     preconditions) are not overflow-checked and compute in `T` too.
   * fixed-width operands of DIFFERENT types (`x: u8 + y: i16`) → `int`:
     exact. Rust exec code cannot express this (a type error); Verus types it
     as spec arithmetic over the mathematical integers, so that is its only
     meaning. Each operand is read with its own type's signedness; `/` and
     `%` are Euclidean (Verus `int` division); `& | ^` are the exact
     two's-complement result (computed at `max(width + [unsigned])` bits,
     where they cannot overflow, then read signed). A comparison reads the
     result at that exact value.
   * an `int`/`nat` operand or declared type → exact (unchanged). A
     conditional with one fixed-width branch and one `int` branch is the
     integer each branch denotes (the fixed-width branch read with its own
     sign), like a mixed arithmetic node.
   * anything else keeps the declared type; what the encoder cannot model is
     refused (`Unknown`), never guessed.
2. **A literal never changes its value by being typed.** A suffixed literal
   has its suffix's type. An unsuffixed literal — the `Int { width: 32 }`
   placeholder — takes the type of the peer it meets exactly when its value
   (for `-v`, the literal `-v`, as Rust reads `-128i8`) is a value of that
   type; otherwise it keeps its own type, which makes the enclosing operation
   mixed and therefore exact. A negative literal never becomes unsigned: `-1`
   next to a `u8` is `-1`, not the `u8` negation 255. A closed tree of such
   literals takes the peer's type when EVERY literal in it does, and is then
   that type's arithmetic — Rust's inference types the literals, not the
   tree's value, so `y != 200 + 100` with `y: u8` is `u8` arithmetic, which an
   exec obligation refutes as an overflow. A tree that meets no peer is `i32`
   arithmetic (Rust's default literal type): `(i32::MIN - 0) - 256908456 <=
   0i64` is `Verified` (the `i64` peer types it; -2404392104), and the same
   tree against an untyped `0` is `i32` arithmetic and wraps to 1890575192. A
   tree with a literal beyond `i32` that meets no peer has no `i32` reading and
   is its exact value. Evaluators that cannot see the peer (the pre-solve
   constant fold, `by(compute)`) fold an untyped OPERATION only where every
   type agrees on its value, and otherwise leave it to the solver.
   A CONDITIONAL (`if`/`match`) every branch of which is an untyped literal
   form is one too, whatever its condition: its literals take the peer the
   conditional meets (`is_untyped_literal`). It was a value of its `i32`
   placeholder, so `(if c { 200 } else { 200 }) + y` (`y: u8 == 100`) was a
   mixed, hence exact, addition — no overflow obligation, and `== 300`
   `Verified` — through a `let`, a `match`, a closure argument and a branch
   write `let mut w = 0; if c { w = 200; }` (whose join is such a
   conditional). An untyped operation that holds a conditional has no
   constant value, so the compiler's overflow lint cannot see it, and the
   peer that types it may be one the encoder does not see where the
   operation is evaluated (a later `let z: u8 = w`, the parameter of a call
   it is an argument of): where it meets no peer, its overflow obligation is
   checked in EVERY fixed-width type all its literals fit
   (`check_untyped_conditional_operation_in_every_type`). A binding whose
   initializer is an untyped literal form (`let mut w = 0`) has the type its
   later uses give it (`vc_extraction/untyped_binding_type.rs`: a use that
   unifies it with an operand of a known type fixes it; `i32` only when every
   use is read and none fixes one), or none; a loop that writes it declares
   its loop-head value at that type, and fails closed without one — it was
   declared `i32`, so `w + y` after the loop was mixed again
   (`tests/untyped_literal_form_typing.rs`). An OPERATION of the binding's
   type (`w - 1`, `w >> 1`, `-w`) is a use of it: next to an operand of a
   known type it takes that type (`w - 1 + y`, `(w >> 1) + y`, `let z: u8 =
   w - 1`), and where this reading does not type it (a call or method
   argument, a struct field, a tail, an unascribed `let`) it decides
   nothing, as the bare name there does, so the binding has no type:
   `g8(w - 45)` left a loop-written `w` at `i32` and the loop's `u8`
   overflow unchecked (`tests/misread_residual_soundness.rs`,
   `tests/misread_operation_and_float_form_soundness.rs`). A bitwise `!` of
   an untyped literal form (`!0`, `!w` once `let w = 0` is substituted) is
   refused: its value depends on the type a peer gives it (255 in `u8`, -1 in
   `i32`), and as an `i32` value it made `!0 + y` a mixed, exact addition.
   A TRAIT method called on such a binding types it through its signature
   (`vc_extraction/untyped_binding_method.rs`): `Ord::{max, min, clamp}`
   unify their arguments with it and give their result its type (a result
   typed by its position, like an operation of the binding's type), and the
   `PartialEq`/`PartialOrd`/`Ord` comparisons unify their `&` argument with
   it, either way round (`w.min(y)`, `y.lt(&w)`); any other method decides
   nothing. Rust refuses an INHERENT method on an unconstrained integer
   (E0689), not a trait method, so reading every method call as fixing
   nothing left `w.min(y)`, `w.eq(&y)` and `w.max(1) + y` at `i32` after a
   loop that overflows `u8` (`tests/untyped_binding_method_soundness.rs`).
   An unascribed COPY `let z = <w, or such an operation or method of it>;`
   has the binding's type, so it is read through the uses of `z`
   (`vc_extraction/untyped_binding_copy.rs`): `let z = w << 1; z + y` types
   `w`, an unused `let _m = x.max(1);` fixes nothing, and `let z = w - 45;
   g8(z)` leaves `w` undetermined.
   A SHIFT whose value operand is an untyped literal form (`1 << k`, `255 >>
   k`) is one itself: its value has that operand's type, which the peer the
   shift meets fixes, and its amount is typed apart. As an `i32` value,
   `(1 << k) + y` was a mixed, exact addition, and `!(1 << k)` escaped the `!`
   refusal. A shift by an amount that is not a literal has no constant value,
   so where it meets no peer in its own obligation (`g8(1 << k)`, a returned
   `1 << k`) it is checked in every width its literal fits, like an untyped
   conditional (`check_untyped_nonconstant_form_in_every_type`); the price is
   a refutation of an `i32` shift the program never widens past (`let z = 1
   << k;` with `8 <= k < 32`), which is not `Verified` either way
   (`tests/untyped_shift_literal_soundness.rs`).
   A CONSTANT untyped form is not left to the compiler either: its
   `arithmetic_overflow` lint does not see through a borrow or a closure
   capture (`let a = 200; let r = &a; g8(*r + 100)`, `let f = || a + 100;
   g8(f())`) and does not fire where it is allowed, so those programs compile
   and panic. An exec panic-safety obligation holds its site's value cut out
   of the slot it fills, so the value is typed there where the extractor
   reads the slot's type — the parameter of a file function it is an argument
   of, the result slot of an invoked closure passed there, the type the uses
   of an unascribed `let` of an untyped form give it
   (`__trust_vc_slot_typed::<T>`) — and otherwise marked: a constant untyped
   form that panics in a fixed-width type it may take is refused
   (`ir_lowering/untyped_site.rs`; `tests/untyped_constant_through_borrow_soundness.rs`,
   `tests/constant_untyped_form_allowed_overflow_soundness.rs`). The binding
   of an unascribed `let` of an untyped literal form is typed as Rust infers
   it: at the type its uses give it (a call argument of a file function whose
   parameter type is read types it too; a `let` that shadows the name ends
   its uses), `i32` when none fixes one, and where the uses do not determine
   it its value is marked (`__trust_vc_untyped_binding`, lowered as a
   one-valued conditional), so where it meets no peer it is checked in every
   type it may take and, as a constant, refused when it panics in one: read
   bare, `let a = 200; let r = &a; assert!(*r + 100 > 0); g8(a);` was `200 +
   100` in `i32`.
3. **No substitution retypes a variable.** A pinned integer variable is
   replaced only by a value of its own type (an untyped literal is folded to
   one literal of the variable's type); an `i32` variable is never replaced by
   an untyped-looking literal, since `Int { width: 32 }` cannot tell `-128i32`
   from the placeholder `-128`. The equality stays asserted. The same holds for
   EVERY substitution of a value for a variable — an axiom instantiated at a
   witness (ground pool, candidate-model revalidation, interpreted-trigger
   replay), an inlined call's argument for its parameter, `by(compute)`: the
   value is pinned at the variable's type (`ir_lowering::pin_substituted_value`;
   an `i32` one by an identity cast). A literal substituted bare was typed by
   the peer it met at the use site, so `spec fn v(x: i32) -> int { (x +
   2147483647) * 2i64 }` instantiated at `x := 3` read the closed tree `3 +
   2147483647` as `i64` arithmetic while the axiom's `i32` sum wraps — two
   readings of one definition, which made every VC that mentions `v`
   `Verified` (also `(x + 1) * 2i64`, with no precondition at all, through the
   revalidation witnesses).
4. **`===` compares values**: mixed-sign operands are compared as integers.
5. **Shifts** keep the left operand's type. The amount is read unsigned at
   its own width and is never truncated: under `by(bit_vector)` (and wherever
   no shift-bound obligation is checked) an amount `>= width` shifts every
   bit out (`<<` and unsigned `>>` give 0, signed `>>` the sign fill) — the
   SMT-LIB semantics the encoder documents. An amount wider than the value is
   saturated to the width, not bit-extracted (`1u8 << 256u16` was `1u8 << 0`).
6. **A value is bound only at a type that holds it.** A `let x: T = v`, a
   spec function's defining axiom `f(..) == body` for a fixed-width result
   `T`, and a `wrapping_*`/`checked_*`/`saturating_*` method (`fn(self, rhs:
   Self) -> Self`) take a value of type `T` — or an untyped literal form that
   fits `T` — and refuse any other integer type (`ir_lowering::int_binding`;
   Rust and Verus reject such a program). A `let x: int` / `nat` lifts a
   fixed-width value to the integer it denotes. The value's term used to be
   registered at the declared width and sign whatever it was: `let t: u8 = y`
   (`y: i16 == -1`) read 65535, `let t: u8 = -1` read 4294967295, and a
   definition `fn m(x: u8, y: i16) -> u8 { x + y }` equated a `u8` with the
   integer -1, which made the axiom set inconsistent. A `match` is typed like
   a conditional, from all its arms (`derive_arms_int_type`).
   A `nat` holds only non-negative values, at every site: an untyped literal
   binds at a `nat` only when its value is one (`bind_untyped_literal`, the
   one literal rule of `int_binding` and `bind_call_argument`), and a spec
   function's `nat` result is checked like a fixed-width one. Only OPERANDS
   make an exact join `nat` — `+ * / %`, `& | ^` and a conditional over
   `nat`s — never the node's declared type; `nat - nat` and `-nat` are `int`
   (`exact_join_type`, `arith_result_type`). Measured before (r9 verifier, at
   44e93f72 and 50b27076): a declared `nat` was returned whatever the other
   operand was, so `let v: nat = x1 + x2` (`x2: int == -9`) held -2 and the
   oracle's own default seed decided `let v: nat = x1 / x2` (`x2: int`); `spec
   fn gneg() -> nat { -1 }` verified `gneg() == -1`, and `let v: nat = -1; v
   == -1` was `Verified` (`tests/integer_typing_nat_bindings.rs`). A `nat`
   difference returned from a `nat` function is written `(a - b) as nat`, as
   Verus requires.
7. **A literal the source types `i32` is an `i32`.** `200i32` (and `-128i32`)
   lowers to an `Int { width: 32 }` literal pinned by an identity cast, in the
   syn lowering and the proc-macro codegen alike, so it is never read as the
   unsuffixed placeholder: `x_u8 + 200i32` is mixed, hence the integer 300.
   In the typed seam `Int { width: 32 }` cannot tell the two apart; a node a
   producer DECLARED `i32` whose `Int { width: 32 }` literal the placeholder
   rule would type by its other, non-`i32` operand has two readings with
   different values and is refused (`Unknown`).
8. **A spec function returning `int` is exact throughout its plain
   arithmetic.** The source catalog promotes `+ - * / %`, unary `-`, `if` and
   `match` in such a body to `int` (Verus's expected type), including
   arithmetic under a node that is already `int` because its operands have two
   types: `fn w(x: i32) -> int { (x + 1) * 2i64 }` computes `x + 1` exactly,
   as `fn d(x: i32) -> int { x + 1 }` does. Explicit finite-width boundaries
   (`as T`, `wrapping_*`, bitwise and shift operations, finite-returning calls)
   keep their own semantics. Only the RESULT context is changed; the same
   expression written inline in an `ensures` computes same-type operations in
   `T` (the deviation below).
9. **Only what was checked is assumed.** An exec obligation's overflow
   predicates are checked by a separate pass and then assumed in the main
   query. A demand-inline retry expands spec-function bodies the separate
   pass never expanded, so it assumes no overflow predicates: it used to
   assume "`x0 * 3` does not overflow" from an inlined `spec fn q(x0: u16) ->
   int { 18252i16 / (x0 * 3) }`, which is false at `x0 == 34862`, making the
   exec `ensures q(x0) == 7` vacuous.
10. **A value is widened or lifted by ITS OWN sign, and nothing else's.**
    Every place that brings a bit-vector to a wider width, or lifts it to the
    integer it denotes — a `match` arm and a conditional branch at the join's
    type, an arithmetic/bitwise/comparison operand, a `wrapping_*` operand, a
    cast's operand, a `let`/call-argument/element binding, a sequence index —
    reads the sign of THAT subterm's own IR type
    (`encoder::width_coercion::OwnSign`, which only the subterm's expression
    or the collection it was read from can produce; it has no `or`). A
    subterm whose type fixes no sign is refused where it would be widened
    (only a same-width `==`/`!=` needs no sign). A term nobody knows the type
    of (a value met by a collection at the TERM level) is never widened or
    narrowed at all: element, key and value arguments are bound at the
    collection's element type while their expressions are known
    (`bind_element_arguments`). A `match` whose type is one fixed-width `T`
    widens EACH ARM to `T` by its own sign before the `ite` chain is built.
    Measured before (r6): the chain widened the accumulated later arms by the
    MATCH's sign, so `match s { 0 => y_i16, _ => x_u8 }` (typed `i16`) read
    `x == 200` as -56 — `== -56` Verified, `== 200` refuted — through spec-fn
    results, proof/exec `ensures`, `let`s and `assert`s, guarded arms and
    enum scrutinees (`i128`/`u8` read 255 as -1; the `u8`-first arm order is
    typed `int` and was right). Measured before in the same audit: a cast
    read its operand at the node's declared `from_ty`, not the operand's
    type (typed seam `Cast { x_u8 == 200, from_ty: i8 } == -56` Verified);
    a sequence index was always zero-extended, so with `s.len() == 300` and
    `i: i8 == -1`, `s[i] == s[255]` was Verified. Read in code and closed
    without a measured wrong verdict: `contains`/`index_of` registered the
    needle with the ELEMENT's sign, and the term-level store/key coercions
    widened by a `term_widths` sign or truncated a wider value. A literal
    `match` pattern is typed by its scrutinee (it was narrowed to a width
    guessed from the variables in scope — `match s_u8 { 0 => y_i32, .. }`
    was a sort error, `Unknown`). It is BOUND at the scrutinee's type by rule
    11's `bind_call_argument`: a literal of any suffix by its value, which the
    scrutinee's type must hold (only the widths used to be compared, so
    `match x_u8 { -1i8 => 1, _ => 0 }` took the arm at 255 and `match y_i8 {
    200u8 => .. }` at -56). An element READ (`s[i]`, `m[k]`, `get`, `first`,
    `last`, `choose`) is a value of its collection's element type: a typed-seam
    node declaring another integer type is refused, like a variable whose node
    type disagrees with its declaration (with `s: Seq<u8>`, `s[0] == 200`, the
    read declared `i8`/`i16`/`i64` was sign-extended: `s[0] == -56` Verified,
    through a `let`, an array, a map `get` and `first`/`last` —
    `tests/integer_typing_element_reads.rs`). A `take`/`skip` COUNT is lifted
    to a length by its own sign and, when it can be negative, carries `0 <= n`
    (`count_as_length`): it was lifted unsigned, so `n: i8 == -1` read 255 and
    `s.skip(n).len() == 45` (`s.len() == 300`) was `Verified`, and an `int`
    count had no lower bound (`s.skip(-1 as int).len() == 301` —
    `tests/integer_typing_counts_and_patterns.rs`). That obligation is
    checked only where obligations are (an assertion's overflow pass, a
    typed assumption's side conditions); a spec function's DEFINING AXIOM, a
    broadcast lemma and every ground/trigger re-encoding drop them. So the
    LENGTH of every length-decreasing view — `take`, `skip`, `subrange`,
    `drop_first`, `drop_last` — is itself exact only inside its domain (`0 <=
    n <= len`, `0 <= i <= j <= len`, `len >= 1`), each bound read at its own
    value, and an unspecified `nat` outside it (an uninterpreted function of
    the receiver and the counts, clamped at 0; `length_within_domain`), as
    Verus's `subrange` is. Measured before (r9 re-verifier, at 3319adfa):
    `spec fn tkl8(s: Seq<u8>, n: i8) -> int { s.take(n).len() as int }` made
    `tkl8(s, -1) < 0` `Verified` and `requires tkl8(s, -1) >= 0 ensures
    s.len() == 7` vacuous (introduced by count_as_length, which routed signed
    bit-vector counts into the exact lift), and `spec fn skli(s, n: int) ->
    int { s.skip(n).len() as int }` verified `skli(s, -1) == 301`, as did a
    `subrange(-1, len)` wrapper (`tests/integer_typing_count_axioms.rs`).
    The guard has a price in solver time: inside a quantified axiom the
    domain must itself be derived (measured under load: an in-domain
    `tkl8(s, n) == 5`, `n == 5`, took ~160 s where the unguarded definition
    took ~30 s, and a conjunction of two such goals timed out), and a goal
    about an out-of-domain length can only be `Unknown` after the solver's
    budget. An `update(i, v)` of a sequence is the same shape: its length is
    the receiver's only for `0 <= i < len` (`i` read at its own value), and
    an unspecified `nat` otherwise (Verus's `axiom_seq_update_len` requires
    the domain); a fixed-size array keeps its type's length. Measured before (r10, at 9fd50172): `spec fn upl(s: Seq<u8>, i:
    int) -> int { s.update(i, 0u8).len() as int }` made `upl(s, -1) == 300`
    and `upl(s, 300) == 300` (`s.len() == 300`) `Verified`
    (`tests/integer_typing_update_domain.rs`). The unspecified length is a
    function of EVERY argument of the operation, an update's stored value
    included (it ignored the value, so `s.update(-1, 0u8).len() ==
    s.update(-1, 7u8).len()` was `Verified` — r10 re-verifier). The same
    class read through an ELEMENT (recorded open at cf28b009, each
    `Verified` through a spec function at 9fd50172 and cf28b009) is closed
    WHERE THE ENCODING DROPS ITS OBLIGATIONS (`drops_domain_obligations`: an
    assumption — a spec function's defining axiom, a broadcast, a ground or
    trigger re-encoding — and a demand-inline retry, rule 9): there an
    out-of-domain update is an unspecified sequence, a function of the
    update's arguments (`s.update(-1, 0u8)[0] == s[0]` and `s.update(2^64,
    7u8)[2^64] == 7` were `Verified`); a `take`/`skip`/`subrange`/`drop_*`
    view ties its cells to the receiver's only inside its domain, and each
    ground seed only below its length (`s.take(-1)[0] == s[0]`,
    `s.skip(-1)[1] == s[0]`, `s.take(2)[3] == s[3]`); and a read at an `int`
    index outside the carrier's `[0, 2^64)` is an unspecified value of the
    receiver and the index instead of the cell the index wraps to (`at(s,
    -1) == at(s, 2^64 - 1)`, `at(s, 2^64) == s[0]`) —
    `tests/integer_typing_out_of_domain_cells.rs`. There a read of a
    sequence that SHARES its carrier with another one (a `store` — an
    update, a push — or a conditional over such) at any index outside `0 <=
    i < len` (the bound the checked encoding pushes, read at the index's own
    value) is an unspecified value of the receiver and the index too: past
    the end, an in-domain update's carrier is its receiver's, so
    `s.update(5, 7u8)[300] == s[300]` (`s.len() == 300`) was `Verified`,
    where Verus relates an update's cells to its receiver's only in domain
    (`axiom_seq_update_different`; `tests/misread_value_soundness.rs`). A
    variable's or a function result's carrier is a function of that value
    alone and keeps its plain read (guarding it too turned ground-pool and
    broadcast instances over a sequence variable into solver `unknown`s). Where the obligations are
    checked (an assertion's own pass) the checked domain makes the two
    encodings agree, and the unguarded one is kept: making the update's
    cells unspecified there with an array-valued conditional (measured at
    cf28b009) turned in-bounds exec read-after-writes
    (`tests/array_dependent_index_bounds_77.rs`,
    `vec_literal_tuple_field_index_assignment_capability.rs`, two
    `exec_index_bounds_faithful` lib tests) into solver `unknown`s, and so did
    the length guard alone on a fixed-size array.
11. **A call argument is bound at its parameter's type only where that type
    holds it** (`ir_lowering::bind_call_argument`, the one rule of the source
    lowering, the encoder's typed calls and exec-callee contracts): an
    argument of the parameter's type as is; a literal — unsuffixed or
    suffixed — whose VALUE the parameter type holds, at that type (an
    unsuffixed tree is typed literal by literal, rule 2); a fixed-width
    argument every value of which the parameter type holds, widened by its
    own sign (rule 10); a fixed-width argument at `int` (an unsigned one at
    `nat`) lifted; anything else refused (`Unknown`). Pinned by
    `tests/integer_typing_call_arguments.rs`. Decided cases the r5
    re-verifier listed as rule-inconsistent: `spec fn inc32(x: i32) -> int {
    x + 1 }` gave `inc32(255u8) == 0` Verified — the `u8` term met `x + 1`
    unbound and wrapped at 8 bits — while rules 3 and 8 give 256, which is
    what it now is; `spec fn id8s(x: u8) -> int { x }` wrapped a literal the
    parameter cannot hold when negative (`id8s(-1) == 255` Verified) but kept
    it exact when too large (`id8s(300) == 300` Verified) — both are now
    refused, as are `id8s(b)` for `b: i16` or `u16` and `idn(b)` (`nat`) for
    `b: i8`. The exec-callee path already refused a variable of another type
    and a suffixed literal of another type; it now binds by the same rule
    (`255u8` for a `u32` parameter is `255u32`, `a: u8` is `a as u32`).
    A COMPOSITE parameter (a collection, a tuple, a datatype) holding an
    integer takes only a value of the same integer type at every integer
    position (a composite is a carrier of bits: `g0(p: Seq<u8>) -> u8 {
    p[0] }` applied to `t: Seq<i8>` with `t[0] == -56` gave `g0(t) == 200`
    `Verified`); a parameter mentioning a type parameter is instantiated at
    the call. An INLINE function's call binds its arguments the same way
    before its body is substituted (`substitute_inline_calls`; an argument
    its parameter's type cannot hold leaves the call unexpanded, and the
    dispatch refuses it), and the validator (rule 13) checks every call's
    arguments at the root: `fid(q: u8) -> u8 { q }` inline, applied to `y:
    i8 == -56`, substituted `y` bare, so `fid(y) < 0` was `Verified` — in the
    exec lane even for the NON-inline `fid`, whose demand-inline retry
    re-encodes the call inline (r10 re-verifier;
    `tests/integer_typing_call_argument_binding.rs`,
    `integer_typing_composite_arguments.rs`). The panic-safety check of an
    invoked exec closure binds each argument the same way, at the closure's
    parameter type (`|a: u8|`, else the `fn(u8) -> R` / `Fn(u8) -> R` /
    `SpecFn<u8, R>` its binding declares): substituted bare, `let f = |a:
    u8| a + 100; f(200)` checked `200 + 100` in `i32`
    (`tests/misread_residual_soundness.rs`). A parameter neither written nor
    declared (`|a|`, `let f: _ = ..`, an alias `let f: F8 = ..` the lane does
    not read) takes only an argument that carries its own type
    (`__trust_vc_self_typed`, `ir_lowering::SELF_TYPED_MARKER`): an untyped
    literal form, or a name bound to one, is refused, because Rust types that
    parameter from EVERY call and use of the closure (`let f = |a| a + 100;
    f(y_u8); f(200)` is a `u8` addition). The check never RETURNS on a binding
    type it does not read: the definition-site planner counts the call as the
    closure's coverage, so a return left the body checked nowhere (`let f:
    F8 = |a| a + 100; f(y)` at `y == 200u8`;
    `tests/closure_argument_type_soundness.rs`).
12. **A body `let` binds its value at its ascribed type.** The extractor
    models `let v: T = value;` by substituting `value` for `v`, and the
    substituted text used to keep its own type: `let v: int = x_u8; v + 1
    == 256` (`x == 255`) was refuted and `v + 1 == 0` Verified, and `let v:
    u8 = y_i16` was accepted. It is now substituted as
    `__trust_vc_let_bound::<T>(value)`, lowered through rule 6's
    `int_binding` (lifted, typed, or refused). The pre-solve constant
    evaluator binds a folded `let` the same way (it substituted the value
    bare: `let v0: u8 = -764435651; v0 == ..` came back a decided
    counterexample — found by the oracle below at seed 1), and `by(compute)`
    no longer rebuilds a literal of a type that cannot hold its value.
    EVERY pattern shape and spelling binds at the ascription
    (`render_bound_at_ascription`): `let (v): T` as `let v: T`; a file `type`
    alias of an integer type through the alias table every parameter uses; a
    tuple ascription over a tuple literal component by component (the path
    every tuple pattern takes, through its synthetic `let src: (T0, T1)`);
    any other tuple ascription that names an integer type only at exactly its
    own type; and a struct/tuple-struct/slice pattern under such an ascription
    is refused. Only a bare identifier with a primitive/`int`/`nat` ascription
    was bound: with `x: u8 == 255`, `let (v, w): (int, int) = (x, x)`, `let
    (v): int = x` and `type MyInt = int; let v: MyInt = x` each made `v + 1
    == 0` `Verified` (`tests/integer_typing_let_patterns.rs`).
    Every OTHER binding site binds the same way
    (`tests/integer_typing_binding_residuals.rs`, r9 at 3319adfa and r10 at
    9fd50172, each `Verified` before): a literal constructor (`seq![..]`,
    `vec![..]`, `[..]`, `Some(..)`, `Ok(..)`/`Err(..)`, `&..`) under an
    ascription that names an `int`/`nat` position — or, where the file
    decides fixed widths (the declared-width lane's closed-world admission),
    any integer type — binds each element at the element type, and any other
    value under such an ascription is bound as a whole (`let v: Seq<int> =
    seq![2147483647]` and `let v: Seq<i64> = seq![2147483647]` read `v[0] +
    1` in `i32`; `let s: Seq<nat> = seq![-1]` held -1 and `let v: Seq<u8> =
    seq![300]` held 300); in a file that does not decide widths (no file
    context, a glob, an item macro), where a `u8` need not be the primitive,
    no width is given to a fixed-width all-literal composite's literals and
    it is REFUSED at the marker (its `i32` placeholder reading is no width at
    all: `let v: Seq<i64> = seq![2147483647]` read `v[0] + 1 == -2147483648`
    `Verified` there, and when cf28b009 routed assignments through the same
    exemption `v = seq![300]` under `Seq<u8>` held 300 — a regression the
    r10 re-verifier measured); a `choose!` is bound at the ascription like
    any value (`let v: (u8, u8) = choose!(|t: (int, int)| t == w)` held
    `w.0 == 300`); an ASSIGNMENT `v = e` or `v op= e`
    substitutes its value bound at the ascription of the binding `v`
    RESOLVES to — the innermost `let` in scope, whatever its pattern, alias
    or shadowing, else the parameter's declared type — deferred
    initialisation included (`let mut v: nat = 0; v = -1`, `let mut v: int =
    0; v = x_u8`, `let v: u8; v = y_u16`, and a shadowed `v`, a `let`
    shadowing a parameter, `let mut v: N` for `type N = nat`, `v -= 1`,
    which the exactly-once seed this replaces missed). EVERY WRITE into a
    typed slot goes through the one binder `bind_written_value`: a binding
    with an ascription binds at it, a parameter at its declared type, and
    every other slot — an unascribed `let` (`let mut w = v; w = x`), a `mut`
    pattern binding (`if let Some(mut v) = o`, a `match` arm), a write
    through `&mut` to its referent (`*r = x`), a tuple or struct FIELD (`t.0
    = x`, `s.f = x`, `v[i].0 = x`; a component of a written tuple
    ascription binds at that component type) — binds LIKE its witness,
    `__trust_vc_bind_like(witness, value)`: the value the binding held when
    first written (or its projection; a pattern binding's is the
    scrutinee's projection), whose type the lowering derives and binds the
    value at by rule 6's `int_binding` — the `let` marker's rule, which never
    widens (`v = x_i8` into an `i32` binding is refused; the oracle's
    generated write sites found the call-argument rule's widening there) —
    refusing a value that type cannot hold (an untyped literal witness, `let
    mut i = 0`, is typed by what it holds, as Rust infers it; a witness the
    lowering cannot type refuses the write). The slot's type is read from the
    witness's SHAPE (`ir_lowering::slot_type_like`): only a witness that IS
    an untyped literal form — a literal, a conditional of literals, a
    sequence literal of literals, or such a component of a tuple literal —
    takes the written value's type there; a literal the witness merely
    MENTIONS fixes nothing (the first binder returned the value bare for any
    witness mentioning one, so the index of `let mut w = s[0]`, `s:
    Seq<int>`, left `w = x_u8` bare and `w + 1 == 0` `Verified`, deferred
    `let mut w; w = s[0];` too, and `t = (x_u8, 5)` into `let mut t = (v,
    0)` held `x` at `u8`). Each of
    these wrote its value bare (r10 re-verifier, with `x: u8 == 255`, all
    `Verified`, each honest twin refuted: `v + 1 == 0` after `*r = x`, `t.0 =
    x` under `(int, int)`, `w = x`, `v = x` in `if let Some(mut v) = o`;
    `t.0 = -1` under `(nat, nat)` held -1 —
    `tests/integer_typing_write_sites.rs`, and the lane-off and `choose!`
    forms in `integer_typing_write_sites_lane_off.rs`). A write through an
    `&mut` alias of a struct field or a collection cell stores that one bound
    value in the owner and in every alias: the alias kept the right-hand side
    as written, so `let r = &mut s.g; *r = 200; *r + 100` (`g: u8`) and the
    same through `&mut v[0]` (`v: Vec<u8>`) read an untyped 200 and missed
    the overflow, and `*r = x_u8` through `&mut s.f` (`f: int`) read `*r + 1
    == 0` in `u8` (`tests/integer_typing_alias_writes.rs`), and a write
    through one alias of a field (`let r = &mut s.g; let q = &mut *r; *q =
    y;`) left the others (`*r`) at the field's old value; a write no handler
    models is never dropped at the one assignment funnel (`assign_expr`): its
    binding is poisoned, as a projected compound write's is, so every later
    read of it fails closed (a named field of an indexed element, `v[0].g =
    x`, was dropped, and `v[0].g == 1` read the pre-write element); a
    `&mut` to a place that reaches a callee by any spelling — the literal
    `&mut s.g`, a `&mut` alias binding (`let r = &mut s.g; swap(r, ..)`,
    whose place is its recorded target), a cast (`&mut s.g as &mut u8`) or a
    reborrow (`&mut *(&mut s.g)`, `&mut *r`) — frames the place's root
    alike, for an unresolved callee (`std::mem::{swap, replace, take}`) and a
    resolved one (`set0(r)` havocked only the alias), where each dropped
    the write; an alias whose place is not recorded (a moved `let q = r;`)
    is refused as an argument, and a `&mut` borrow destructured by a tuple
    pattern (`let (r, q) = (&mut s.g, &mut t);`), which bound `r` to the
    VALUE of `s.g`, poisons the place and shadows the names
    (`tests/mut_place_alias_write_soundness.rs`); in general a `&mut` to a
    field, a cell or a dereference that no modelled consumer owns — the
    recorded alias of `let r = &mut s.g;` or `r = &mut s.g;`, a direct write
    `*(&mut s.g) = v`, a resolved callee's argument whose root the call
    rebound — lends the place to code the lane does not follow (a
    conditional, a cast, a tuple, an array, a struct literal, a `match`
    scrutinee, a method argument such as `x.clone_into(&mut s.g)`), and
    poisons its root where it is borrowed; a `&mut` alias NAME stored in a
    holder (`let p = (r, 1u8);`) or passed to a method this file declares no
    signature for (`x.clone_into(r)`) poisons its target; and a method called
    through an alias (`let r = &mut s.g; r.add_assign(1u8)`, `(*r).take()`,
    `r.inner.bump()`) that the receiver framing reads as writing the alias
    poisons the alias's target, as the same call on the place itself did
    (`tests/mut_place_unrecognized_borrow_soundness.rs`); a
    pattern binding the extractor does not project is never read as an OUTER
    binding of its name (the identity shadow named that binding's symbol: `if
    let Some(mut v) = o { v + 1u64 }` and `|v: u64| v + 1u64` were checked
    against a parameter `v < 10`; these three in
    `tests/misread_write_soundness.rs`); a closure parameter ascribed `T`
    binds its argument at `T` (`(|a: int| a + 1)(x_u8) == 0`),
    and an inlined closure's result binds at its result type (its `-> R`, or
    the `R` of the `SpecFn<A, R>` / `Fn(A) -> R` / `fn(A) -> R` its binding
    declares; `let f: SpecFn<int, nat> = |a: int| a;` gave `f(-1) < 0`); a
    loop models a name it writes as the declared variable of that name, so a
    loop that writes a `let` or pattern binding shadowing a declared variable
    at another (or an undetermined) type is refused (`let mut w: u8 = 0` over
    a `w: u64` parameter was havocked as the `u64`); a
    reference `let r: &mut T = &mut x` is an alias, so `T` must be the type
    of the local it names, followed through every alias (`let r = &mut x;
    let q: &mut int = r;`) and refused when either is not determined; an
    ascription the lowering cannot resolve (`self::MyInt`, `m::MyInt`,
    `Id<int>`, a generic `Wrap<int>`) binds no integer-holding value; and a
    spec function's COMPOSITE result holds its body at every integer
    position (`spec fn as_i8(s: Seq<u8>) -> Seq<i8> { s }` made
    `as_i8(s)[0] == -56` `Verified` for `s[0] == 200`).
13. **The typed IR is validated whole, before it is encoded.** Every node
    that carries a type — a literal's, an integer node's, a conditional's or
    `match`'s, a collection operation's result, an element read's, a `let`'s,
    a cast's `from_ty`, a variable's, a call's result and arguments — is a
    producer's claim, and one validator (`ir_lowering::validate_ir_typing`) re-derives
    every node's type from its children, bottom-up, at every depth, and
    refuses (`Unknown`) any claim that disagrees: a literal its type cannot
    hold (the placeholder `Int { width: 32 }` holds any value; a signed
    magnitude under `-` is the negated literal), an integer node whose
    declared type is not the one its operands derive, a composite built by a
    type-preserving operation / `let` / conditional / `match` from values of
    another integer type, an element read at another type than its
    receiver's element type, a variable read at another type than its
    binder's, a call read at another result type than its declaration or
    passed an argument its parameter's type cannot hold (rule 11), a cast
    whose `from_ty` is not its operand's type — whatever that type is, a
    `char`, a type parameter or a collection as well as an integer (only
    integer `from_ty`s were compared: with `s: Seq<u8>`, `s[0] == 200`, `s as
    Seq<i8>` declared `from_ty: Seq<i8>` read -56, and `y: i8 == -56` cast
    from a declared `char` to `u32` was 200, a lie that also reached a `take`
    count — `tests/integer_typing_seam_casts.rs`), two composites of
    different integer types compared, and the two collections of a binary
    operation (`concat`, `union`, ..., `subset_of`, `superset_of`: `st:
    Set<u8> ∋ 200`, `st ⊆ t: Set<i8>` made `t.contains(-56i8)` `Verified`). A collection
    operation's result is the type the lowering's one typing rule
    (`infer_collection_op_type`) derives from its receiver and arguments; a
    closure's `SpecFn` type is its parameters' and its body's; a join (`let`,
    conditional, `match`) holds its operands' integer types in BOTH
    directions, so one declared at a type parameter, `Poly` or an opaque type
    does not FORGET them; an element read needs a receiver with an element
    type, and a map key is bound at the key type. It runs on the tree the
    encoder reads — each root as given AND after inline expansion
    (`AYEncoder::prepare_root`; an inline body is never encoded as an axiom,
    so it is validated where it lands), before substitution and
    normalization — and on each goal `by(compute)` is asked to evaluate or
    the constant evaluator is asked to fold (it decided `Cast {
    3132225413u32, from_ty: char } != -12` `Verified` before any validation —
    found by the oracle at seed 7), so the syn lowering and the typed seam
    pass the same check; the syn
    lowering declares derived types (a `match` its arms' join). Measured
    before (r10 verifier, at 9fd50172): with `s: Seq<u8>`, `s[0] == 200`, a
    `to_set`/`to_multiset`/`dom`/`view`/`map_values`/`fold_left`/`Set::map`/
    `Map::map_values` result declared at `i8`, a `map_values` closure
    declared to return `i8`, a conditional/`let`/`match` declared at `T`,
    `Poly` or an opaque type then read at `i8`, and `m[-56i8]` of a `Map<u8,
    u8>` each gave -56 (or the value at key 200); and an inline body's `p[0]`
    declared `i8` (or `p.take(1)` declared `Seq<i8>`) was `Verified`
    (`tests/integer_typing_derived_results.rs`). Measured before (r9 re-verifier, at A =
    50b27076 and B = 3319adfa alike): the element-read check trusted the
    RECEIVER's declared type, so with `s: Seq<u8>`, `s[0] == 200`, reading
    `i8` through `take`/`push`/`subrange`/`reverse` declared `Seq<i8>`, a
    `let`/conditional at `Seq<i8>` or a map `insert` declared `Map<u8, i8>`
    gave -56 (14 false `Verified`, 14 false refutations,
    `tests/integer_typing_declared_claims.rs`), and `IntLit { -1, nat } < 0`,
    `let v: nat = IntLit { -1, nat }; v < 0` and `IntLit { -1, u8 } ==
    255u8` were `Verified`.

14. **A Rust float is never an exact real.** An unsuffixed float literal is
    lowered as the exact `real` it is next to a `real` peer; a Rust `f32` /
    `f64` rounds, and its `as` to an integer truncates toward zero and
    SATURATES (NaN is 0) where a real cast floors and wraps. So a float slot
    (`let f: f64 = ..`, an assignment to one) refuses an exact or integer
    value, an exact real is never cast to a fixed-width integer, and an
    arithmetic operation or comparison over unsuffixed float literals alone
    (`0.1 + 0.2 == 0.3`, once `let a = 0.1` is substituted) is refused:
    `let f: f64 = 300.0; f as u8 == 44` and `-1.5 as i8 == -2` (Rust: 255,
    -1) and `0.1 + 0.2 == 0.3` were `Verified`
    (`tests/misread_value_soundness.rs`). A conditional, `match` or block
    every value of which is such a form, and a value written to a binding
    bound to one (`let mut a = 0.0; a = 0.1;`), are such forms too; and a
    form held by a tuple, an array or an array repeat (`[0.1; 2]`), a `vec!`
    or `seq!` literal, a `Some`/`Ok`/`Err` payload, a `Box`/`Rc`/`Arc`
    payload, or a struct or enum-variant field not declared `real` (a generic
    `struct W<T> { x: T }` takes the literal's own float type) is refused,
    since its component is read back as the exact real (`let p = (0.1, 0.2); p.0 + p.1 == 0.3`, `let a = if
    c { 0.1 } else { 0.1 }; a + 0.2 == 0.3` and `vec![0.1, 0.2]` sums were
    `Verified`; `tests/misread_residual_soundness.rs`,
    `tests/misread_operation_and_float_form_soundness.rs`; `[0.1; 2]`,
    `W { x: 0.1 }.x + 0.2 == 0.3` and `*Box::new(0.1) + 0.2 == 0.3` too,
    `tests/float_holder_soundness.rs`).

The integer-typing ORACLE (`tests/integer_typing_oracle.rs`) checks rules
1-12 mechanically: it generates every integer-role `TrustVcExpr` variant
(`ir::integer_surface::EXPR_VARIANTS`, generated from one exhaustive match
inside trust-vc-core, so a new variant cannot compile unclassified and a
new integer-role variant fails the oracle's coverage test until generated)
and every binding site, through both frontends, exec and non-exec, spec-fn
bodies and results, every width and sign, against an exact `i128`
evaluator of this section. Its default seed (`0x06_ac1e_0924`) was red where
it was committed (9bee642c: source BodyProof case 52, rule 6 above); its
`nat` model now follows rule 6 too — a literal meeting a `nat` takes `nat`,
`+ * / %` and a join over `nat`s stay `nat`, `-` and negation give `int`, and
`let x: nat = -1` is generated (and must be refused). It also generates
(rules 10 and 13) `take`/`skip` counts of a pinned-length `Seq<u8>` — at
the top level and inside a spec function's body, every count type, the
count often out of `0..=len`, where the length is an unspecified `nat` that
no comparison some `nat` falsifies may be `Verified` about — typed-seam
literals declared at a type that cannot hold them, and element reads through
a chain of receivers (`take`, `push`, `let`, a conditional) with a lie at a
random depth; and on the typed seam a node whose declared integer type is
not the one its operands derive is refused. Every WRITE site of rule 12 is
a site of its own in the source frontend's body modes, each shape
generated in turn and binding the tree at a random slot type — an
assignment, a compound assignment, a deferred `let`, a write through `&mut`
(to an ascribed and to an unascribed binding; to a struct field and to a
`Vec` cell, read back through the alias), a tuple, struct and
parameter field write, a write to a binding typed by its initializer (a
value, an element read) or by its first write, and to a `mut` pattern
binding of an `if let` and of a `match` arm. The oracle's site and shape
lists are derived from their enums, and each site's frontend is classified
by an exhaustive `match`, so a new site is covered by construction. One
source file in four imports a glob (the declared-width lane off), in which
nothing may bind differently; on the typed seam one spec function in three
is INLINE (its argument bound before the body is substituted) and a cast is
declared from a `char`, a type parameter or a sequence (refused).

**Deviation from Verus, deliberate and bounded:** Verus types same-type
fixed-width spec arithmetic as `int`; trust-vc computes it in `T` (rule 1,
first bullet) outside quantifier bodies, where it is exact (FV-B,
`arith/int_arith.rs`), and outside an `int` result context (rule 8), where it
is exact too. That is the pre-existing, documented model
(recursive spec-fn bodies, `tests/recursive_specfn_fixedwidth_overflow.rs`,
and the integer-model note both pin it); moving same-type spec arithmetic to
`int` is the open item recorded in `docs/archive/replacement-progress.md` ("encode
spec/contract/calc obligations int-mode"), not part of this change. Every
regression pinned for this change is false under BOTH readings.

Measured at 8bbef1af (the tree before this change): the source frontend typed
`x + y` by its left operand and `if c { x } else { y }` by its then-branch, so
`requires x == 0, y == -1, z == 256` (`x: u8`, `y`/`z: i16`) verified
`x + y >= z` and refuted the true `x + y < z` (the sum read as 65535); the
typed seam verified `29878u16 * -256 >= 28688i16`; `-x0 < z` (`x0: i32 ==
-128`, `z: i8 == 0`) verified after substitution; `255u8 === -1i8` verified;
`1u8 << 8u32 == 0` and `1u8 << 256u16 == 1` both verified under
`by(bit_vector)`.

Measured at 2f792110 (rules 3 and 6-9; `tests/integer_typing_specfn_axioms.rs`,
`integer_typing_literal_sites.rs`, `integer_typing_source_probes.rs`,
`integer_typing_typed_seam_probes.rs`, `integer_binding_soundness.rs`,
`integer_typing_survey.rs`): `spec fn w(x: i32) -> int { (x + 1) * 2i64 }`
made `ensures w(x) == 0 && w(x) == 1` (no precondition) and `ensures(false)`
after mentioning `w` verify — the revalidation lane instantiated the axiom at
the bare literal `x := 2147483647`, whose closed tree `2147483647 + 1` the
`i64` peer typed exactly while the quantified axiom wraps, and the promotion
to `int` stopped at the mixed node so the axiom did wrap; an exec caller of
`spec fn q(x0: u16) -> int { 18252i16 / (x0 * 3) }` at `x0 == 34862`
verified `q(x0) == 7` (an unchecked "no overflow" assumption); `let t: u8 =
-1; t > 1000`, `0u8.wrapping_add(-1i16) > 1000`, a `u8`-declared match over
a `-1i16` arm `>= 256`, `mixsum(0, -1) == 65535` (`-> u8 { x + y }`), `x +
200i32 == 44`, `-> u8 { if c { -1 } else { 0 } }` with `ensures c ==> result
== 7`, and `inc(-1)` bound at a `u8` parameter all verified.

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
   the differential-oracle + native-theory track from `docs/archive/grand-strategy-ay.md` —
   owned in ay (`ay-z3-parity`), not here.

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

- `docs/archive/design-rustc-driver-frontend.md` — the **Verus-compatibility front end**
  (standalone rustc-driver) under this north star; its `lower.rs` seam is shared
  with the in-Trust path.
- the internal grand-strategy-ay notes — the **Problem-B** program (differential oracle +
  native theories); composes with this design (item 6.4).
- `docs/archive/TRUST_NATIVE_VERIFIER_V2.md` — the ownership boundary between tRustc and
  trust-vc; this design realizes it.
- the internal execution plan (100% of Verus's capabilities at full or
  superior; updated 2026-09-17) — it replaced the retired internal
  Verus-replacement plan and the parity-to-100 program notes that this bullet
  named before.

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
  re-checked the resolution trace and exported a ~350-char Alethe rendering of it —
  Alethe is an output format here, not the thing being re-checked); a refuted goal
  carries none.
  *This is the soundness property Verus's black-box Z3 cannot provide, now realized
  at the front-end seam.*
- **The standalone rustc-driver skeleton** (`feature = "rustc-driver"`, Trust `rustc_private`) —
  the Verus-compat front end (`src/driver.rs`): `Callbacks::after_analysis(tcx)` →
  type-checked signature → `DriverFn`; fail-closed until THIR body/contract
  lowering lands.
- **Superiority capabilities #2–#7** — `src/{compiler_facts,cache,collections,
  strings,layout,tactics}.rs`, each feature-gated with its own test suite (see the
  Built table in §5a). All seven verify together via `targo --unverified test
  -p trust-vc-driver --features all-capabilities` (**59 tests, 0 failed**, as
  measured on 2026-06-14 with the then lane-less spelling; see the note under
  the §5a Built table), default
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
