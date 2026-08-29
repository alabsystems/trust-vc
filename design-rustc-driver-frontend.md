# Audit & Design Memo: `trust-vc-driver` — a rustc-driver front end for trust-vc

> **North star:** `design-trust-proof-backend.md` — trust-vc is Trust's proof
> backend; this memo designs its **Verus-compat front end** (the parity benchmark/gate).

> **Status:** Design proposal + first increment landed (2026-06-14), **adversarially
> reviewed**. This memo audits a project that has already done deep, rigorous work
> and made a deliberate Path-1 (independent verifier) / Path-2 (reuse Verus VIR)
> decision; it shows how a rustc-driver front end *composes* with that decision
> rather than reversing it. Where the synthesized design's central claims were
> refuted or caveated under review, this memo **corrects** them inline rather than
> papering over them. Adopting the driver as the *primary* front end is a
> maintainer decision (§8), in the same spirit as the 2026-06-02 Path decision in
> the internal grand-strategy-ay notes.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0
**Pinned context:** Verus ref `a40d57c73650cd3648b09386bfdb96ab5c270626`;
manifest `evals/verus/verus-tests.json`; ay pinned in `[workspace.dependencies]`.

---

## 1. Bottom line

trust-vc's verification core — the typed IR (`TrustVcExpr`), the `vc/` seam, the
encoder, ay, and the `trust-vc-kernel` certificate checker — is genuinely
front-end-agnostic **at the IR surface**, so a standalone **`trust-vc-driver`**
that lowers rustc's typed THIR/MIR into that same IR is architecturally viable
and is **categorically not** the rejected Path 2 (it reuses *zero* Verus code; it
depends on rustc, the language's own compiler, exactly as Verus, Prusti, Kani,
and Creusot do). The driver attacks the project's dominant bottleneck — the
**front-end information ceiling** (Problem A): trust-vc today has zero rustc usage
and reconstructs name/trait/type resolution from single-file `syn` syntax,
round-tripping its type system through strings. **But the payoff is bounded and
must be sold honestly:** the driver addresses the *primary* blocker on roughly
half the gap corpus (an upper bound on what becomes *addressable*, not a lower
bound on what *promotes*), it does nothing for the solver residual (Problem B),
and several headline claims required correction under review — notably that the
encoder is **not** syn-free at solve time, that the evidence gate's fingerprints
are **syn-string-keyed** (so "same IR ⇒ same gate input" is false today), that the
route-A length fix is **front-end-independent** (not a driver win), and that the
"critical recursive-spec unsoundness" the sequencing argument rested on is
**already fixed** on the current pin. The driver is a real, well-scoped Problem-A
instrument; it is **not** a path to `Proven` by itself.

---

## 2. Why 100% Verus parity is hard (root causes, ranked)

### Rank 1 (dominant): the front-end information ceiling — Problem A

trust-vc has **zero** rustc usage in its current tree (0 hits for
`rustc_private`/`TyCtxt`/`rustc_middle`/`rustc_hir` across `crates/`; 310 files
reference `syn::`). Its entire front end is a single-file `syn` source-reparser
that hand-rebuilds the four artifacts rustc hands Verus for free: name/module
resolution, trait resolution, the typed `Ty` table, and
const-eval/monomorphization. The tax is concrete and spread across a dozen
`trust-vc-core` modules, each approximating one rustc duty:

- `mode_index.rs` — name resolution from filesystem conventions.
- `mode_paths.rs:84` — method resolution "without type info, we match by method
  name only."
- `recursion_graph` — a *name-only* call graph + Tarjan SCCs.
- `trait_catalog.rs:76-101` — scans `.rs` files off disk for the substrings
  `"trait_spec"` / `"trait_impl"`.
- `trait_expand.rs:104` — supertrait elaboration by last path segment.
- `extern_spec_registry.rs:24` — `FileLocal`-only.

The keystone failure is that **the type system literally round-trips through
strings**: `local_vars_helpers.rs::extract_type_string` (`:359-387`) does
`quote!(#path).to_string()` and *erases* `&T` / `&mut T` (`:377`); then
`ir_type_parse.rs` re-parses that string with a hand-written depth tracker
(`type_syntax.rs:16`) and strips references *again* (`:425`). const-eval is a
single `.parse::<usize>()` (`ir_type_parse.rs:74`); the test at
`ir_type_parse_tests.rs:419` proves a symbolic `[u8; CONST_ARRAY_LEN]` is
rejected. The lossy fallback `TrustVcType::Opaque(String)` (`ir.rs:503-509`)
exists precisely because the parser sees spelling, not types, and `verify_typed()`
must reject opaque-typed contexts to stay sound.

Within Problem A there is a **fundamentally unobtainable** sub-tier (no
single-file hand code can close it):

- MIR borrowck facts — `&mut`/prophecy, `&mut` generics, regions — erased at the
  type-string boundary.
- Cross-crate trait/type identity and associated-type projection — `std`/`vstd`
  metadata lives in another *compiled* crate, not in any `.rs` file trust-vc
  reads.
- const-eval / monomorphization of non-literal expressions.

The remainder of Problem A is **laborious but bounded**: the `&` in `Seq<&S>` is
*in* the syntax (deliberately erased today); const generics as opaque nats,
generic datatypes as parametric IR, and single-file trait/`Default`/operator
resolution are engineering, not missing information.

**This is what the driver attacks.** rustc gives all four artifacts by
construction.

### Rank 2: the solver ceiling — Problem B (survives any front end)

Per `grand-strategy-ay.md` (the Path-2 passage), even the maximal front-end move
— adopting Verus's *whole* front end — "reduces the entire program to Problem B:
make ay solve Verus's SMT2." The theorem handed to ay is the same regardless of
who emits it. The bounded gap set:

- **B1** — native-collection symbolic reasoning + extensional equality.
  `set/src/lib.rs:74-93` fail-closes `set.map`/`filter`/`fold`/comprehension as
  `OUT_OF_FRAGMENT_OPS` ("unsound to decide today, fail-closed"); the missing
  piece is a comprehension/lambda carrier over the element domain.
- **B2** — SAT-side MBQI counterexample construction. ay ships `mbqi.rs`
  quick-check but degrades to `Unknown` on model construction, so `multiset
  *_fail` returns `Unknown`, not `Counterexample`.
- **B3** — quantifier-instantiation starvation. Native-seq concat-assoc on
  symbolic operands is still `Unknown` because unrelated quantified axioms hit
  the instantiation limit before the seq-theory conflict fires.
- **B4** — nonlinear NIA/NRA. `ay-algebraic/saturate.rs` exists (Groebner) but is
  **not wired** into `nia`/`nra` (it is not a dependency of `ay-dpll`/`ay-nia`/
  `ay-nra`/`trust-vc`); full CAD is deferred (#8335).

A *refuted* non-gap: the old "ay e-matching doesn't fire for uninterpreted/seq
sorts" was empirically disproven (parity doc `:10-14`). Do not spend solver
effort there.

### Rank 3: the diagnostic-fidelity ceiling

About half of the upstream gap cases are *negative* tests asserting byte-exact
compiler error strings (`assert_vir_error_msg` / `assert_rust_error_msg`). The
doc states trust-vc "a verifier, not a rustc fork, generally cannot reproduce"
these. Today trust-vc hand-reconstructs them byte-for-byte
(`ir_lowering/diagnostic_parity.rs`, present, ~20 reconstruction fns). This is the
*cleanest* information-ceiling case for the `syn` reparser — and the one root
cause where re-hosting on rustc (which **owns** the diagnostic emitter) collapses
most of the surface. It is ranked third because, unlike Ranks 1–2, the cause is
per-string toil that the superior design retires *structurally for the rustc-class
subset only*.

> **Correction (CLAIM 7, see §7).** `assert_vir_error_msg` strings are
> Verus-VIR-specific and are *already* reproduced today **without any driver**;
> only `assert_rust_error_msg` (genuine rustc borrow/type errors) is driver-gated.
> The diagnostics ROI bucket is therefore smaller than a naive "half the negative
> tests" reading; measure the true split by grepping the pinned Verus checkout for
> the two macros before sizing it.

**Why the ranking matters:** Rank 1 is what the driver attacks; Rank 2 is what it
provably *cannot*; Rank 3 is the cheap structural win bundled with Rank 1's fix —
for the rustc-class subset.

---

## 3. The superior design: `trust-vc-driver`

A standalone `rustc_driver` front end that lowers rustc's typed THIR/MIR into
trust-vc's **existing** typed IR, feeding the **same** encoder / ay / kernel /
gate. It is a **new producer for an existing seam**, not a new back end, and
reuses **zero** Verus code.

### What is KEPT vs REPLACED

| Layer | Disposition | Evidence |
|-------|-------------|----------|
| `TrustVcExpr` IR (`ir.rs`, `ir_expr.rs`) | **KEPT** — IR *type* is syn-free | `ir.rs` 0 `syn::`; `ir_expr.rs` only doc-comment mentions |
| `vc/` seam (`context`, `builders`, `obligation`, `verify`) | **KEPT** | `vc/` 0 `syn::` |
| Encoder typed dispatch (`encode_trust_vc_expr`) | **KEPT** | `ir_encoder/mod.rs` only doc-comment mentions |
| ay solver + `trust-vc-kernel` certificate checker | **KEPT** — untouched by any front-end swap | `kernel/lib.rs:5-17` |
| Evidence gate (`cargo trust-vc evidence`, `ReplacementVerdict`) | **KEPT** — measures trust-vc's own corpus run | `evidence.rs` |
| `syn` → IR lowering (`ir_lowering/*`, `lower_syn_expr`) | **REPLACED** by THIR/MIR → IR (per construct, ratcheted) | — |
| `RustToSmtTranslator` (`translator.rs`) | **DROPPED** — legacy proc-macro plumbing, unreachable from the verify path | — |
| 4 residual *string-typed* IR channels | **MIGRATED to typed** (see "Residual" below) | — |

The live verify path is typed end-to-end at the IR surface:
`VerificationContext::verify()` (`vc/verify.rs:22`) →
`AYEncoder::verify` (`encoder/mod.rs:203`) → `prepare_context` → `verify_typed` →
`resolve_condition_typed(&TrustVcExpr)` → `encode_trust_vc_expr` — a closed typed
dispatch over every variant. A rustc driver sits exactly where `lower_syn_expr`
sits.

> **Correction (CLAIM 1, see §7).** The strong claim "**no** string re-parse
> during solving" is **false** and is corrected here. Fourteen files under
> `encoder/` still reference `syn::`, and several do `syn::parse_str →
> lower_syn_expr` *inside* the solver gate on verify-reachable paths:
> `encoder/eval/condition.rs` (trigger encoding, called live from `fuel.rs` and
> `broadcast.rs`), `encoder/trait_encoding_axioms.rs`,
> `encoder/verification/trait_conformance_contracts.rs`, and
> `encoder/verification/invariants/frame_condition.rs` (loop guards). These
> re-parse *internally generated/stored* condition strings (triggers, trait
> bodies/contracts, loop guards) — a residual string round-trip baked into the
> encoder, **not** a front-end coupling. The IR-surface and `translator.rs` facts
> hold (`translator.rs` is reachable only from front-end codegen, never the
> encoder/solver); "the encoder is syn-free at solve time" does **not**.

### Residual typed-ification the driver must also retire

Four channels still carry conditions as **strings** and force a lazy
`syn::parse_str` even on the typed path; the driver must pre-lower these to
`TrustVcExpr`:

1. `ProofObligation.condition` — dual-carrier fallback with `typed_expr`
   (`obligation.rs`).
2. Trigger patterns — `Vec<Vec<String>>`.
3. Loop guards — `HashMap<String,String>`.
4. `TraitMethodDecl.requires`/`ensures: Vec<String>` + `default_body:
   Option<String>` (`ir.rs:352-357`), re-parsed in `trait_encoding_axioms.rs` and
   `trait_conformance_contracts.rs`.

Retiring these removes the last syn touchpoints in `encoder/` and is what makes
the back half *actually* syn-free at solve time — a precondition the synthesized
design under-stated.

### ASCII pipeline diagram

```
 AUTHORING (kept permanently)                 READING (new producer)
 ┌───────────────────────────┐               ┌──────────────────────────────┐
 │  syn proc-macro DSL        │               │  trust-vc-driver  (nightly)  │
 │  #[proof] requires!        │               │  rustc_driver::Callbacks     │
 │  ensures! decreases Tracked│               │  → run_compiler              │
 └─────────────┬─────────────┘               │  → after_analysis(tcx)       │
               │                              │  → THIR (tcx.thir_body)      │
               │ default --frontend=syn       │     [spec/contract preds]    │
               │ (existing, never displaced)  │  → optimized_mir (later)     │
               ▼                              │     [exec/loop/borrow]       │
 ┌───────────────────────────┐               └──────────────┬───────────────┘
 │  ir_lowering/*            │                              │ --frontend=driver
 │  lower_syn_expr(&syn::Expr)│      trust-vc-extract        │ THIR→TrustVcExpr
 └─────────────┬─────────────┘   ┌──────────────────────────┘   (the only
               │                 │                               rustc-coupled
               └────────►  ┌──────▼──────────────────────┐       lowering)
                           │   TrustVcExpr  (typed IR)    │  ◄── ONE shared seam
                           │   ir.rs / ir_expr.rs (syn-   │
                           │   free at the IR surface)    │
                           └──────────────┬──────────────┘
                                          ▼
                           ┌─────────────────────────────┐
                           │  VerificationContext / vc/   │
                           │  encode_trust_vc_expr        │
                           └──────────────┬──────────────┘
                                          ▼
                           ┌─────────────────────────────┐
                           │  ay solver  →  UNSAT cert    │
                           └──────────────┬──────────────┘
                                          ▼
                           ┌─────────────────────────────┐
                           │  trust-vc-kernel checks cert │  ◄── soundness edge,
                           └──────────────┬──────────────┘      front-end-invariant
                                          ▼
                           ┌─────────────────────────────┐
                           │  cargo trust-vc evidence     │  ◄── UNCHANGED gate
                           │  ReplacementVerdict          │      (own corpus run)
                           └─────────────────────────────┘
```

### Driver shape (from reference architectures)

Take Verus's **non-fork** driver shape combined with tRust's proven
rustc-internal mechanics:

- **(a)** A thin `rustc_driver::Callbacks` binary (own `main`,
  `#![feature(rustc_private)]`) calling `run_compiler` — like Verus's
  `rust_verify`, **never** an in-tree fork (unlike tRust).
- **(b)** Hook `after_analysis(tcx)` for a fully-populated `TyCtxt` (typeck +
  trait resolution complete), return `Compilation::Stop` in verify-only mode.
- **(c)** Lower from **THIR** (`tcx.thir_body`) — post-typeck, fully
  type-annotated, pre-desugaring — so overflow-checked arithmetic, match arms,
  user types, and contract expressions are still recognizable and map cleanly to
  source spans (MIR has desugared them away; tRust chose MIR precisely because its
  target is imperative/borrow verification). **Pragmatic hybrid:** lower
  spec/contract predicates and pure spec-fn bodies from THIR; descend to
  `tcx.optimized_mir` only later for exec/loop/borrow reasoning — tRust validates
  this split.
- **(d)** Discover specs via **tool attributes** — register a tool namespace and
  scan `tcx.get_all_attrs` for `#[trust_vc::requires(..)]` etc. (tool attrs
  survive verbatim through typeck), or keep the `verus!`-style proc macros that
  lower specs into companion items the driver reads back. **Not** a fork-only
  `tcx.trust_contracts` query.
- **(e)** Make ghost code survive typeck via the builtin/vstd pattern: ship
  `trust-vc-std` spec fn / `Ghost<T>` / `Tracked<T>` / `forall` / `exists` as real
  well-typed Rust, erased before codegen like Verus's `EraseMacro`.
- **(f)** Generics: start monomorphic (lower in `body.typing_env`, fail-closed on
  free params as tRust does), then adopt Verus's polymorphic **Poly-sort**
  encoding (`vir/src/poly.rs` model: box type params into a universal SMT sort
  with `I`/`%I` casts; trait bounds become axioms) to avoid combinatorial
  monomorphization and match ay's quantifier behavior.

### Isolation discipline

Exactly **one** new rustc-coupled crate, `crates/trust-vc-driver` (+ a
`trust-vc-extract` lowering core) — the only crates importing `rustc_*` —
structurally identical to tRust's `trust-mir-extract`/`convert.rs` decoupling, the
single most reusable mechanic. The in-tree skeleton already splits a **stable**
`lower.rs` seam (compiles on pinned stable 1.95.0; part of the default workspace
build) from a **nightly-only** `rustc-driver` feature with its own
`rust-toolchain.toml`. The rest of the workspace and the authoring DSL stay on
stable.

### Why this is NOT the rejected Path 2 (the load-bearing distinction)

Path 2 (`grand-strategy-ay.md`, REJECTED) reuses Verus's `VIR → AIR → SMT2`
pipeline, making trust-vc "Verus-frontend + ay-backend, a re-backend, not an
independent verifier," which "would have to redefine" the evidence gate. The
driver reuses **nothing** from Verus: it swaps the front-end *input* (`syn` syntax
→ rustc THIR/MIR) but feeds the **same** independent `TrustVcExpr → ay Term → ay
solver → trust-vc-kernel` pipeline and the **same** gate.

Independence is from **Verus**, not from rustc. Depending on rustc — the
language's own compiler — is what every serious Rust verifier does (Verus, Prusti,
Kani, Creusot) and is categorically different from reusing a *competitor's
translation*. The soundness edge (ay UNSAT certificates independently checked by
`trust-vc-kernel`) sits downstream of the solver and is untouched by any
front-end swap.

> **Correction (CLAIM 2, see §7).** The gate is computed over trust-vc's own
> **corpus-run report + manifest**, *not* over `TrustVcExpr` (which appears
> nowhere in `evidence.rs`). The verdict logic — `Proven` iff `blocking_reasons`
> is empty — is genuinely **unchanged** by the driver. But the sub-claim "no gate
> input would change shape if a second front end emits the same `TrustVcExpr`" is
> **false as stated**: the per-obligation gate fingerprint is `sha256` of a
> **syn-rendered condition string** (`quote!(#expr).to_string()`, pinned in
> `expected_cases`), and the typed `condition` is a placeholder `<typed:{name}>`.
> Two front ends emitting the same IR generally produce *different* fingerprints.
> Wiring the driver into the gate therefore requires new bridging that
> canonicalizes typed obligations into matching fingerprints, or re-pins
> `expected_cases`. The "not Path 2" distinction is substantive and survives; the
> "free gate compatibility" corollary does not.

---

## 4. ROI and honest bounds

### Headline

The driver plausibly clears the **primary currently-gating blocker** on roughly
**half** the gap corpus (estimate 45–55%, central ~52%; ~58 of 111 files),
combining FRONTEND-TYPES wins (THIR/trait/const/monomorph unlocking whole
categories) with rustc-class DIAGNOSTICS parity. **These are text-classification
estimates from manifest `reason`/`known_gaps` fields and the project's own gap
maps — not per-case re-verification.**

> **Count correction — ITSELF SUPERSEDED (2026-08-28).** The manifest no longer
> carries a `status` field at all, so the `status`-vs-`classification`
> discrepancy this note is built on no longer exists; the live
> `classification` split is **46 ported / 106 unsupported-gap / 4 not-applicable
> / 0 unclassified** of 156. The per-cluster arithmetic below is keyed to the
> 2026-06-14 base of 111 and should be re-derived, not quoted. Original note
> follows.
>
> The working notes' headline "112 unsupported-gap" reflects the
> manifest's `status` field; the `classification` field holds **111**
> unsupported-gap / 41 ported / 4 not-applicable / 1 unclassified (= 156). Both
> are present in `evals/verus/verus-tests.json` (verified); this memo uses the 111
> classification base. `real.rs` was promoted (manifest ported = 41).

### What the driver unlocks (Problem A + bundled diagnostics), by cluster

| Cluster | Driver-unlockable | ~files | Why |
|---------|------------------:|-------:|-----|
| #2785 datatypes/generics/assoc/async | ~75% | ~24 | Strongest cluster; ay's dt theory (constructor-clash/occurs-check) already present — this is front-end breadth |
| #2784 concurrency/mut-refs | ~60% | ~11 | `mut_refs_*` family is borrow-ck/move-ck front-end work THIR+MIR provide |
| #2779 collections front-end slice | ~50% | ~8 | const generics, iterator desugaring, `Default`/trait resolution |
| #2778 bitvector/layout/`size_of` | ~50% | ~4 | ay BV theory complete; mostly rustc-class diagnostic-string parity |
| #2777 proof constructs | ~30% | ~10 | Only the lifetime/mode/diagnostic slices |
| #2775 / #2780 | — | ~2 | Regression / wrapper |

Sum ≈ 58/111 ≈ 52%. **Plus** the route-A soundness/decidability win on collection
lengths — an *encoding* change at the encoder that removes the spurious
length-overflow mask (see §5, and the CLAIM-5 correction: this is **not** a driver
win).

### What the driver does NOT touch (residual ~45–50%, pure Problem B)

B1 native-collection symbolic reasoning + ext-eq (the symbolic tail of #2779); B2
SAT-side MBQI counterexample finding; B3 instantiation starvation; B4 nonlinear
NIA/`integer_ring` (Groebner unwired, CAD deferred). This residual dominates #2777
(quantifier/MBQI/broadcast completeness, ~22), the symbolic-collection tail of
#2779 (~8), #2778 nonlinear/float (~4), #2784 atomics/state-machines (~7), #2780
ghost-state macros (~2). The general principle: a perfect front end still emits
VCs ay must discharge. (Empirically re-confirmed: diagnostic-free #2779 files —
`sets`, `multiset`, `btree` — return `Unknown` for *solver-side* reasons even when
fed a typed program.)

### The honest downward adjustments

1. **The 52% is an UPPER bound on what becomes *addressable*, not a lower bound on
   what *promotes*.** *(Correction, CLAIM 4.)* The driver removes only the
   information barrier; each construct still needs a built THIR→IR lowering **and**
   encoder semantics **and** (often) solver power. The per-file gate is
   **all-or-nothing** (every gap file mixes positive proofs and negative cases; it
   promotes only when *all* obligations discharge), so doubly-blocked files — many
   of #2779 — still need ay work to flip. The *realized* promotion fraction from
   the driver alone is a much smaller, separate lower bound. The synthesized
   framing labeled the 52% a "lower bound"; that is on the wrong side and is
   corrected here.

2. **The DIAGNOSTICS leg is smaller than a naive split suggests.** *(Correction,
   CLAIM 4/7.)* `assert_vir_error_msg` (Verus-VIR-specific) strings are *already*
   reproduced byte-for-byte by `ir_lowering/diagnostic_parity.rs` **without any
   driver**; only `assert_rust_error_msg` (true rustc borrow/type errors) is
   driver-gated. Lumping both into "rustc-class DIAGNOSTICS" overcounts the
   driver-attributable share.

3. **The driver currently realizes ZERO end-to-end promotions.** *(Correction,
   CLAIM 4.)* `crates/trust-vc-driver/src/driver.rs::lower_fn` unconditionally
   returns `DriverError::UnsupportedContract` (no THIR body/contract lowering yet)
   and `map_ty` handles only bool/int/uint; the seam test
   (`tests/lower_end_to_end.rs`) constructs `DriverFn` by hand and never invokes
   rustc. So the proposed `verify_function_from_file` probe measures the *syn*
   engine's solver-blockedness (a valid double-blockedness proxy) — not driver
   realizability. The driver is at "first increment" (signatures only).

### Bottom-line ROI bound

Justify the driver on **Problem-A grounds** (breadth + the `assert_rust_error_msg`
diagnostics + the route-A encoding soundness), **not** as a path to `Proven` by
itself. It can be built fully and the gate can still read `NotProven` if the
residual solver work (B1–B4) has not landed. The driver's single highest payoff is
#2785 (~24 files); its near-zero payoff is #2777's quantifier core and the
symbolic-collection/nonlinear residual, which remain a dedicated ay native-theory +
MBQI-completion + Groebner program. This is consistent with — and slightly more
conservative than — the project's own prior estimate (front-end breadth ~60–70%
MBQI-independent + solver power ~30+).

---

## 5. Ratcheted migration plan

The driver runs **alongside** the `syn` path behind a flag; promote
cluster-by-cluster; **the evidence gate is the ratchet**; the `syn` DSL stays for
authoring permanently.

### Phase 0 — soundness sequencing (must precede driver promotions)

> **Correction (CLAIM 6, see §7).** The "critical recursive-spec unsoundness" the
> synthesized sequencing argument depended on (recursive spec fn without
> `decreases` proving false) is **already fixed** on the current pin — commits
> **6550fa2** (source-catalog path, which the corpus/evidence gate uses) and
> **52cf444** (proc-macro path, defense-in-depth) are in HEAD's history (verified),
> and the committed regression test `tests/soundness_recursive_axiom.rs` passes
> (`Counterexample`, not `Verified`). The fix is fail-closed and Verus-faithful: a
> self-recursive spec fn with no `#[decreases]` is left *uninterpreted* rather than
> having its defining axiom asserted. **The Phase-0 blocker on the soundness axis
> is therefore already satisfied** (the fix predates the driver skeleton).
>
> The legitimate *residual* is narrower: the fix gates the axiom-**production**
> sites (`spec_function_catalog.rs` / `spec_expand.rs`), not the
> **consumption** sites (`fuel.rs:113`, `setup_broadcasts.rs:65`), whose code is
> literally unchanged and sound only because upstream no longer emits the bad
> axiom. A sink-side `decreases` assertion at the fuel encoder is worthwhile
> belt-and-suspenders (and would guard a future third production path, e.g. the
> `when_used_as_spec` sibling-helper axiom at `vc_extraction.rs:3407`), but it is
> **defense-in-depth, not an open false-`Verified` path.** The general methodology
> — "do not build a new front end on top of an open false-proving hole, lest new
> surface area mask it" — remains correct in the abstract; its concrete trigger
> does not exist on this pin.

What *does* remain a genuine Phase-0 item: **Route A** (Int-sorted collection
lengths). Replace the fixed-width-BV "concat length no overflow" obligation
(`collection_seq_inline.rs:82`; the same BV no-wrap pattern at
`collection_methods.rs`, `indexing.rs`, `collection_axioms.rs`, `multiset.rs`,
`flat_map.rs`; root length `Sort::bitvec(pw)` at `encoder/mod.rs:442`) with
Int-sorted lengths. Route B (`assume bvadd(l,k) >= l`) was **unsound** and reverted
(commit 2050567); the near-MAX vacuity guards in
`tests/collection_len_nearmax_soundness.rs` are the permanent regression. Separate
length-arithmetic (→Int) from index-arithmetic (stays BV) across ~43 sites with
`bv2int`/`int2bv` bridges.

> **Correction (CLAIM 5, see §7).** Route A is **NOT** "the one encoding win a
> typed front end delivers." It is a purely **encoder-internal Sort choice**:
> change `declare_const(Sort::bitvec(pw))` to `Sort::Int` at `mod.rs:442` and
> propagate. The branch keys only on `var.ty` (`Seq`/`Array` via `is_collection()`),
> which the **existing `syn` front end already produces** — the Int-length pattern
> is *already implemented in the same file* for native-strings (`mod.rs:506`) and
> native-seq (`mod.rs:583`), gated purely by Cargo features, consulting **no**
> rustc/THIR data. This memo's own §2.2 lineage classifies
> `collection_seq_inline.rs` as front-end-*independent* Problem B. **Route A is
> achievable today on the syn path and must not be deferred behind the driver.** It
> belongs in Phase 0 for soundness; crediting it to the driver mis-attributes a
> Problem-B encoding fix to Problem A — and risks deferring a sound, available fix
> behind a heavyweight nightly driver it does not need.

### Phase 1 — stand up the driver behind a flag (additive, never displacing)

`crates/trust-vc-driver` (own pinned-nightly `rust-toolchain.toml`) + a
`trust-vc-extract` THIR→`TrustVcExpr` lowering crate — the only rustc-coupled
crates. **First increment = the existing skeleton:** lower a *minimal typed
integer fragment* (bool/int/uint signatures) into a `VerificationContext` via the
stable `lower.rs` seam, calling the existing `VerificationContext::verify()`. The
`syn` proc-macro DSL stays as the **authoring** surface — users still write
`#[proof]`/`requires!`/`ensures!`/`decreases`/`Tracked`; the driver is how the
verifier **reads** the program, not how users write specs. Both front ends coexist
behind a cargo flag (`--frontend=driver` vs the default `syn` path).

To wire the driver into the gate later, the skeleton must (a) implement
THIR-body/contract lowering beyond the current `UnsupportedContract` stub, and
(b) **bridge typed obligations to the gate's fingerprint scheme** — either
canonicalize `TypedProofObligation` into the `sha256(condition-string)` shape the
manifest pins, or re-pin `expected_cases` for the driver path. (This is the
concrete consequence of the CLAIM-2 correction: the gate is fingerprint-coupled,
not IR-coupled.) The driver must also always supply `typed_expr` so it bypasses
the proc-macro-populated thread-local caches `prepare_context` reads
(`take_pre_built_expr`, `loop_metadata`, `proof_session`).

### Phase 2 — ratchet cluster-by-cluster, gated by evidence

Promote in descending ROI order, each cluster validated by the **differential
oracle** (VC-level diff vs Verus on the *same typed program* — far more meaningful
once both sides start from a typed program rather than syn-vs-VIR) and locked in
by the evidence gate. Order:

1. **#2785** datatypes/generics/assoc/async — the driver's strongest cluster
   (front-end breadth; dt theory already present).
2. The **`assert_rust_error_msg` diagnostics** win — re-host the *rustc-class*
   negative tests on rustc's own emitter, retiring per-string toil in
   `diagnostic_parity.rs` structurally. (Verus-VIR-specific `assert_vir_error_msg`
   strings stay in a thin parity layer.)
3. **#2784** mut-ref/prophecy — fundamentally a borrow-ck/move-ck front-end problem
   THIR+MIR provide.
4. **#2779** front-end slice — const-generic array lengths, iterator desugaring,
   `Default`/trait resolution.

At each step run `cargo trust-vc evidence`; only files that **fully** verify
(front-end **and** solver obligations both discharge) flip to `ported` in the
manifest. `unsupported-gap` remains a failing classification, so the gate cannot
silently regress.

### The ratchet is the gate

No cluster is "done" until `cargo trust-vc evidence` (`--strict` for the full run)
reclassifies its files and `blocking_reasons` shrinks. The verdict logic
(`ReplacementVerdict::Proven` iff `blocking_reasons` empty; `unsupported-gap`
gating) is **unchanged** by the driver because it measures trust-vc's own corpus
run — the sharpest contrast with Path 2. The driver **composes with** (does not
replace) the Problem-B program: the differential oracle + native theories attack
the solver gaps in parallel; the driver attacks Problem A.

### Phase 3 — convergence / retirement (decide up front)

Maintaining two front ends is real duplication. Define the retirement criterion
now: once the driver reaches parity-or-better on a cluster's *reading* (oracle diff
empty on that cluster), the `syn` **lowering** path (`ir_lowering/*`) for that
construct is retired; the `syn` DSL **authoring** surface (the proc macros) is
**kept permanently** as the proof-calculus surface. End state:

> **`syn` = how specs are written; rustc driver = how programs are read;
> ay + kernel = how they are proved and certified.**

---

## 6. Costs, risks, and mitigations

| # | Cost / risk | Mitigation |
|---|-------------|------------|
| C1 | **Large, sustained engineering.** A THIR/MIR→`TrustVcExpr` lowering is comparable in scope to Verus's `rust_to_vir_*` — a multi-month track parallel to the existing front end. All estimates are *by analogy to Verus, not measured*; no THIR/MIR lowering exists yet (current `lower_fn` is a stub). | Ratchet cluster-by-cluster; ship value at each gate increment; reuse tRust's `convert.rs` decoupling pattern. |
| C2 | **Nightly + `rustc_private` maintenance tax.** Unstable interface; every toolchain bump can break the driver. THIR is *less* stable across nightlies and has fewer consumers than MIR. The skeleton already carries unresolved API-drift caveats (`RunCompiler` vs `run_compiler`, attribute matching, `register_tool`) against nightly-2024-12-01. | Scope nightly to the single `trust-vc-driver` crate's own `rust-toolchain.toml`; the rest of the workspace and the authoring DSL stay on **stable 1.95.0**. Standard Verus/Prusti/Creusot cost. |
| R1 | **Does NOT advance Problem B.** If `NotProven` is dominated by solver gaps (collections/quantifiers — which Phase-1 evidence strongly implies are solver-bound), the driver can be built fully and the gate still reads `NotProven`. | Justify on Problem-A breadth + `assert_rust_error_msg` diagnostics + route-A only; never sell as a path to `Proven`. Run the Problem-B program (oracle + native theories) in parallel. |
| R2 | **Soundness sequencing.** A new front end on an unsound encoder inherits and could *mask* the unsoundness. | **Already largely satisfied:** the recursive-spec hole is fixed (6550fa2/52cf444) at the shared axiom-production layer, *below* where any front end plugs in, so the driver cannot re-open or mask it. Land Route A (Phase 0) before driver promotions; add the sink-side `decreases` assertion as defense-in-depth. Route A itself is designed-but-unverified — a mistake separating length-arith (→Int) from index-arith (BV) across ~43 bridge sites reintroduces vacuity. |
| R3 | **Two front ends during transition.** Real duplication; thread-local / proc-macro-populated caches (`take_pre_built_expr`, `loop_metadata`, `proof_session`) read by `prepare_context` must be populated or bypassed by a non-proc-macro driver. | Decide retirement up front (§Phase 3): keep the DSL authoring surface permanently, retire only the lowering per cluster once the oracle diff is empty. Driver must always supply `typed_expr` to bypass the caches. |
| R4 | **Residual string-typed IR channels.** Even with a typed front end, four channels still flow strings (`ProofObligation.condition` fallback, triggers, loop guards, `TraitMethodDecl` requires/ensures/default_body, `ir.rs:352-357`), keeping syn live in 14 `encoder/` files at solve time. | Driver must pre-lower all four to `TrustVcExpr`; effort to typed-ify trait contracts is not yet fully scoped. This is the work that makes the back half *actually* syn-free at solve time. |
| R5 | **Gate fingerprint coupling.** The gate keys per-obligation fingerprints on `sha256(syn-rendered condition string)`, not on the IR. A driver emitting the same IR produces different fingerprints and cannot satisfy pinned `expected_cases` without bridging. | Add a canonicalizer from `TypedProofObligation` to the manifest fingerprint shape, or re-pin `expected_cases` for the driver path. Schedule this in Phase 1 before any driver promotion is claimed. |
| R6 | **Scope creep into full Rust semantics.** A THIR/MIR front end pulls toward implementing the whole language surface. | Hard "supported fragment, fail-closed otherwise" discipline (the existing IR already enforces "no silent drops"); start monomorphic, fail-closed on free params. |
| R7 | **Identity-drift *perception*.** Depending on `rustc_private` superficially resembles the compiler-coupling avoided with Path 2. | The decision record must state explicitly: the dependency is on **rustc** (the language's own compiler, as every serious Rust verifier does), **never** on Verus. Independence (own IR/encoder/translation), the certificate edge (ay + kernel, untouched), and the gate (own corpus run, unchanged) are all preserved. THIR-vs-MIR is unsettled and materially affects how `TrustVcExpr` is populated (THIR for spec fidelity, MIR for borrow/exec; hybrid is the long-term answer). |

**Count / evidence caveats (carry these in any quantitative claim).** The 112-vs-111
discrepancy is the manifest's `status`-vs-`classification` fields (above). The A/B
file-count split and the ~52% ROI are text-classification ranges, **not** per-case
re-verification; the docs repeatedly warn that agent blocker-guesses **overstate**
solver gaps (e.g. `#[trust_vc::inline]` was called a no-op but works).
`MAX_EMATCHING_ROUNDS` is now 16, not the 8 in older docs — round limits are tuned
knobs, so "how starved" claims may be stale. The diagnostic-parity split rests on
docs + the 111 classifications, not a direct grep of the pinned Verus checkout —
measure it directly (`assert_vir_error_msg` vs `assert_rust_error_msg`) before
sizing the diagnostics bucket.

---

## 7. Adversarial review summary

Seven central claims were stress-tested. **Three held with caveats, one held with
corrections to its empirical framing, and three were materially corrected or
refuted.** None of the refutations invalidate the design; each tightens it.

| Claim | Verdict | Resulting correction in this memo |
|-------|---------|-----------------------------------|
| **1.** IR/VC/encoder core is front-end-agnostic; live path is typed end-to-end with **no** string re-parse during solving | **Holds with caveats** | The IR *surface* is syn-free and `translator.rs` is genuinely dead on the verify path; **but "no string re-parse during solving" is false** — 14 `encoder/` files use `syn`, and `eval/condition.rs`, `trait_encoding_axioms.rs`, `trait_conformance_contracts.rs`, `frame_condition.rs` re-parse stored trigger/trait/guard strings *in the gate*. The encoder is **not** syn-free at solve time; the 4 residual string channels must be typed-ified (§3 Residual, R4). |
| **2.** Driver ≠ Path 2; zero Verus code; gate logic unchanged; "same IR ⇒ same gate input" | **Holds with caveats** | Driver ≠ Path 2 and `ReplacementVerdict` logic are **confirmed unchanged**. But the gate is keyed on `sha256(syn-string)` fingerprints, not the IR (`TrustVcExpr` is absent from `evidence.rs`); the typed `condition` is a placeholder `<typed:{name}>`. "Same IR ⇒ same gate input" is **false today**; wiring requires a fingerprint bridge (R5, Phase 1). Driver is also **not yet wired** into `cargo-trust-vc`. |
| **3.** Problem B survives any front end (the ROI ceiling) | **Holds with caveats** | Confirmed empirically: diagnostic-free #2779 files return `Unknown` for solver-side reasons; `OUT_OF_FRAGMENT_OPS` and the unwired `ay-algebraic/saturate.rs` re-verified against the pin. Caveats: the "30–48%" band is an *estimate* overlapping Problem A at the margin (#2777); a better-typed front end may emit *fewer/better-triggered* quantifiers, marginally shifting some B3 cases — so "SMT query *identical* from any front end" is "identical *encoder given identical IR*," not bit-identical across front ends. |
| **4.** ~52% driver-unlockable; all-or-nothing gate makes promotions a **lower** bound | **Holds with caveats** | The all-or-nothing/double-blocked logic is correct and matches the repo's own methodology. **But 52% is an *upper* bound on what becomes *addressable*, not a lower bound on *realized* promotions** (different quantities); the DIAGNOSTICS leg is overcounted (`assert_vir_error_msg` already solved without a driver); the driver realizes **zero** end-to-end promotions today (`lower_fn` → `UnsupportedContract`). |
| **5.** Route-A Int-length is **the one encoding win a typed front end delivers** | **Refuted** | Every *code fact* is accurate, but the *framing* is wrong: route-A is a front-end-**independent** encoder Sort choice (keys on `var.ty`, already produced by `syn`; the Int pattern already exists for native-seq/strings). It is achievable **today** and belongs in Phase 0 — **not** creditable to the driver. The "unverified/soundness-sensitive" half of the claim is correct and retained. |
| **6.** Open critical recursive-spec unsoundness ⇒ Phase 0 must precede the driver or it gets masked | **Refuted** | The unsoundness is **already fixed** (commits 6550fa2, 52cf444 on HEAD; regression test passes with `Counterexample`). The fix is at the shared axiom-**production** layer below any front end, so the driver **cannot** inherit or mask it. The narrow legitimate residual is sink-side defense-in-depth (`fuel.rs`/`setup_broadcasts.rs` unchanged; `when_used_as_spec` sibling axiom unchecked) — **not** a live false-`Verified` path. |
| **7.** Diagnostic parity is structurally retired only for the rustc-class subset | **Holds with caveats** | Correct in direction. Sharpened: `assert_vir_error_msg` (Verus-VIR-specific) is **already** reproduced by `diagnostic_parity.rs` *without* a driver; only `assert_rust_error_msg` is driver-gated. Measure the true split by grepping the pinned Verus checkout before sizing the diagnostics ROI bucket (§4 adjustment 2). |

**Net assessment.** The design's spine survives review: the verification core is
reusable at the IR surface, the driver is a legitimately new producer that is not
Path 2, and the Problem-A / Problem-B division of labor is sound. The corrections
do not weaken the case for building the driver; they (a) demote two "free wins"
(route-A is already available and front-end-independent; the soundness blocker is
already closed) into the Phase-0 column where they belong, (b) reclassify the 52%
as an addressability *ceiling* rather than a promotion *floor*, (c) surface a real
integration cost the synthesized design under-stated (the gate is syn-fingerprint
coupled, and the encoder still re-parses strings at solve time, so the driver's
"syn-free" payoff requires retiring the 4 residual string channels), and (d)
confirm the driver buys **breadth and `assert_rust_error_msg` diagnostics**, never
`Proven` by itself. Build the driver for Problem A; keep the
differential-oracle/native-theory program for Problem B; let the unchanged evidence
gate ratchet both.

---

## 8. The most recent landed increment

`crates/trust-vc-driver/` (workspace member; `rustc-driver` feature OFF by default,
so the gated stable build is unaffected):

- `src/lower.rs` — the driver-independent seam: `DriverFn` (typed params,
  `requires`, symbolic `body_value`, `ensures`) → `VerificationContext` via the
  typed obligation path → `verify()`. Encodes the standard Hoare VC
  `assume(requires) ∧ assume(result == body) ⊢ assert(ensures)`.
- `tests/lower_end_to_end.rs` — **runs the real ay solver** and proves the seam is
  sound, not a rubber stamp: valid postconditions → **Verified**; a false
  postcondition → **Refuted** with a counterexample; multiplication + multiple
  postconditions → **Verified**, tightened false bound → **Refuted**. (`targo test
  -p trust-vc-driver` → 6 passed.)
- `src/driver.rs` (behind `feature = "rustc-driver"`, nightly) — the real
  `rustc_driver::Callbacks`: `after_analysis(tcx)` → find marked fns → map
  type-checked signatures → `DriverFn`. **Signature lowering is wired; THIR
  body/contract lowering is the Phase-2 increment and is fail-closed
  (`UnsupportedContract`) until built** — so the driver promotes **zero** files
  end-to-end today (see §4 adjustment 3).

This demonstrates the load-bearing claim end-to-end: *a typed front-end input
drives trust-vc's existing backend to a sound verdict with no `syn` involved* — at
the IR surface. (The "no syn anywhere" reading is corrected by §3/§7: syn remains
live inside the encoder at solve time until the 4 residual channels are typed.)

---

## 9. Decision required

Like the 2026-06-02 Path decision, adopting the driver as the *primary*
verification front end is a strategic choice for the maintainer:

1. **Adopt** the driver as the path to Problem-A parity (this memo's
   recommendation), running it alongside syn and ratcheting via the gate; **or**
2. **Keep** the driver as an experimental/oracle aid only, continuing syn as the
   primary front end (accepting the §2 ceiling on full parity).

The recommendation is (1) — it is the only architecture on which Problem-A parity
is *reachable* rather than asymptotically approached, it preserves trust-vc's
independence and certificate edge, and it composes cleanly with the existing
native-theory/differential-oracle program rather than replacing it — **with the
honest qualifier that (1) does not by itself reach `Proven`.** Problem B (B1–B4)
remains a parallel, dedicated solver program; the gate can and will read
`NotProven` until that work lands, regardless of how complete the driver is. The
two corrections that matter most for sequencing: land Route A and the sink-side
soundness hardening in **Phase 0** (they are front-end-independent and not the
driver's to deliver), and build the typed-obligation → gate-fingerprint bridge in
**Phase 1** before claiming any driver promotion.
