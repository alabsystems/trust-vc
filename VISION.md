# Vision: trust-vc

> Last updated: 2026-08-28. The shipped version is the workspace version in
> `Cargo.toml` (**0.4.0**); the `v1`/`v2`/`v2.1` labels below are ROADMAP PHASE
> names, not release numbers.
> **PHASE v1 STATUS** — Verus replacement is evidence-gated by `cargo trust-vc evidence`; do not treat 100% replacement as proven until the full report passes. Pure-Rust ay backend; no Z3 and no external SMT solver. (ay still calls `libc` for resource limits and ships `ay-jit`, a self-hosted native-code JIT, on the default path — "pure Rust" means the solver algorithms, not a C/FFI-free dependency closure. GMP/MPFR via `rug` are NO LONGER in the dependency closure — they left `Cargo.lock` at `9d3f8fc5`; arbitrary precision is `num-bigint`. See README "Dependencies".)
> **PHASE v2 NEXT** — Beyond Verus: performance, proof certificates, ay-unique capabilities.
> **PHASE v2.1 ACTIVE** — Native ay theory adoption: IEEE FP, Seq, and String encoder paths have all landed behind opt-in features (`native-seq`, `native-strings`; both `default = []`).

## Problem Statement

Rust verification tooling is fragmented across multiple approaches:
- **Verus** uses Z3 (black-box, no checkable proof artifact) and requires external dependency management
- Trust's **trust-mc** capability provides model checking but lacks proof functions
- Trust's **trust-wp** capability offers separation logic but missing termination proofs

**Core Problem:** Trust needs a proof-calculus backend so that one unified verifier
(model checking + separation logic + proof calculus) delivers comprehensive proof
features over a single pure-Rust SMT backend (ay), emitting independently-checkable
certificates. trust-vc is that backend.

## Mission

trust-vc is **Trust's proof-calculus + SMT backend** — a submodule of the Trust
superproject (a rustc fork; trust-vc lives at `first-party/trust-vc`). Its
destination is to be Trust's proof backend, integrated alongside trust-mc
(model checking) and trust-wp (separation logic) as capabilities within the one
Trust verifier. See `design-trust-proof-backend.md` for the authoritative
design (north star) and `design-rustc-driver-frontend.md` for the
Verus-compat front end.

**R1 (2026-07-11) retired the Verus-replacement goal — and was AMENDED two days
later.** Per the ratified two-language spec-surface design
(the Trust repo's `docs/design/2026-07-09-two-language-spec-surface.md` §6): Trust's one
spec surface is first-class Rust clauses + Clean; engines are invisible behind
trust-router. trust-vc's contribution is the auto-active proof calculus
(triggers/fuel/broadcast/calc!/by(compute)) and the ay-native collection
encodings — not a Verus-compatible user surface. The 156-file corpus remains
as regression material (re-keyed at R4); the evidence gate remains as the
corpus-port instrument.
`docs/capability-audit-2026-07-13.md` §preamble then reinstated the replacement
program in two phases, and the ACTIVE GOAL (author-set 2026-07-15, re-affirmed
2026-07-18) is **100% of Verus functionality at "full or superior"** on the
native surface. Read `CLAUDE.md` and
`docs/execution-plan-100-verus-2026-07-15.md` for the live framing; this
section is kept because the R1 reasoning still governs the *surface* question.

**Why target Verus compatibility:**
- It is a concrete parity benchmark that exercises the whole proof language
- Overlapping features with trust-wp = cross-validation, bug finding, better ideas
- Independent implementations (independent *from Verus*) discover better approaches

**Why better than Verus:**
- Checkable proof certificates (ay's UNSAT resolution trace re-checked by
  trust-vc-kernel) vs Verus trusting a black-box Z3 with no checkable artifact.
  Scope it honestly: the kernel checks propositional resolution plus structural
  EUF (transitivity/congruence) and LRA (Farkas) lemmas; **NIA, BV, Array and
  Seq lemmas are accepted on trust** (`trust-vc-kernel/src/lib.rs:17`) and stay
  in the TCB. Alethe is one of the kernel's EXPORT formats, not an input it
  re-checks.
- One unified Trust verifier (MIR/exec + borrows + model checking + separation
  logic + proof calculus, one engine, one solver) vs Verus = Rust surface + Z3 only
- Native ay decision procedures (Seq/Set/Map/Multiset/String/FP/BV) that sidestep
  Z3's MBQI/quantifier fragility
- No Z3: pure-Rust solver algorithms, reproducible
- Cross-IR portability (the ay-vs-Z3 differential oracle itself now lives in
  ay, as its `ay-z3-parity classify` subcommand — it was extracted out of this
  repo at R1 and is no longer a trust-vc deliverable)

**Unique value:** ay backend (no Z3 dependency), proof certificates, and a proof
calculus that plugs into Trust's other verification capabilities.

## Feature Matrix

The `trust-vc` column records implemented tracked surface area in this
repository. It is not evidence that trust-vc passes the upstream Verus test
corpus. The replacement claim is proven only when the strict evidence report
returns `replacement_verdict: proven`.

| Feature | Verus | trust-vc | trust-mc | trust-wp | Notes |
|---------|-------|--------|------|--------|-------|
| `requires`/`ensures` | ✅ | ✅ | | ✅ | |
| `recommends` | ✅ | ✅ | | | Soft preconditions for spec functions (#2483 closed) |
| `spec fn` | ✅ | ✅ | | ✅ (`#[logic]`) | Recursive via `#[opaque]` + `reveal!()` + inline spec substitution |
| `proof fn` | ✅ | ✅ | | | Recursive via reveal/hide + fuel encoding; postconditions propagate at call sites |
| `decreases` (basic) | ✅ | ✅ | | | Non-negative + strict decrease |
| `decreases` (when/via) | ✅ | ✅ | | | `when` (#2293) and `via` (#534) both verified |
| `extern_spec` | ✅ | ✅ | | | File-local + same-package lookup (#2392 closed) |
| Broadcast/triggers | ✅ | ✅ | | | |
| Spec collections | ✅ | ✅ | | | Full higher-order combinators: Seq (map/map_values/filter/flat_map/fold_left/fold_right), Set (filter/map/mk_map/fold), Map (map_values/map_entries/filter_keys) |
| Reveal/Hide/Opaque | ✅ | ✅ | | | `#[opaque]` + `reveal!()` + `reveal_group!()` + inline spec substitution |
| Choose operator | ✅ | ✅ | | | Skolem UF witness extraction (#2143 closed) |
| Datatypes (enum/struct) | ✅ | ✅ | | | Option/Result UF + recursive ADTs + Multiset (#1942, #2421, #2484 closed) |
| Polymorphism | ✅ | ✅ | | | Poly/Box/Unbox type erasure + trait-bound poly (#2053, #2425 closed) |
| Trait verification | ✅ | ✅ | | | Trait method UF + postcondition axioms + default methods (#2425, #2442 closed) |
| Mutable references | ✅ | ✅ | | | SSA shadow rewrite + place-based reasoning (#2426, #2515 closed) |
| Overflow checking | ✅ | ✅ | | | OverflowBehavior/Div0Behavior/BitshiftBehavior (#2516 closed) |
| Auto triggers | ✅ | ✅ | | | Automatic trigger inference for quantifiers (#2461 closed) |
| SMT pruning | ✅ | ✅ | | | Reachability-based declaration pruning (#2520 closed) |
| Real arithmetic | ✅ | ✅ | | | RealArithOp + Int↔Real conversions (#2517 closed) |
| Model checking | | | ✅ | | |
| Separation logic | | | | ✅ | |
| **Backend** | Z3 | **ay** | ay | ay | |

## Features

### Proof Functions

```rust
#[trust_vc::proof]
fn lemma_distributive(a: i32, b: i32, c: i32) {
    // Proof that a * (b + c) == a * b + a * c
    trust_vc::assert!(a * (b + c) == a * b + a * c);
}
```

### Termination Proofs

```rust
#[trust_vc::decreases(m, n)]
fn ackermann(m: u64, n: u64) -> u64 {
    if m == 0 { n + 1 }
    else if n == 0 { ackermann(m - 1, 1) }
    else { ackermann(m - 1, ackermann(m, n - 1)) }
}
```

### Broadcast Lemmas

```rust
#[trust_vc::broadcast]
#[trust_vc::trigger(factorial(n))]
fn lemma_factorial_positive(n: u64) {
    trust_vc::ensures!(factorial(n) > 0);
}

// Now any use of factorial(x) auto-gets: factorial(x) > 0
```

### Spec Collections

```rust
use trust_vc_types::{Seq, Set, Map};

#[trust_vc::spec]
fn sum_seq(s: Seq<i32>) -> i32 {
    if s.len() == 0 { 0 }
    else { s.last() + sum_seq(s.drop_last()) }
}
```

## ay Encoding

| trust-vc | ay | Notes |
|--------|-----|-------|
| `#[decreases(e)]` | `(assert (< e' e))` with well-founded relation | |
| `#[broadcast]` | `(assert (forall ...))` with `:pattern` | |
| `Float{32}` / `Float{64}` | `(FloatingPoint 8 24)` / `(FloatingPoint 11 53)` | Native FP via ay-fp (#2680 Slice 1) |
| `Seq<T>` | `(Seq T)` native or `(Array BV(ptr_width) T)` with length | `native-seq` feature flag; #2680 Slice 2 |
| `Set<T>` | `(Array T Bool)` | |
| `Map<K,V>` | `(Array K V)` | |
| `Multiset<T>` | `(Array T Int)` | Count-per-element encoding (`encoder/types.rs:49`) |

## Integration into Trust

trust-vc is a submodule of Trust, not a standalone end-product. Its proof
surface integrates into the one Trust verifier — where trust-mc (model
checking), trust-wp (separation logic), and trust-vc (proof calculus) are
capabilities of Trust, sharing the ay solver. Integration is gated by cross-repo
infrastructure already in flight:

1. ~~trust-vc maintains a versioned `MergeBundle` handoff contract.~~ ✅ MergeBundle v4 with `FuncDeclMeta`, `FuelAxiomMeta`, `BroadcastLemmaMeta` (#2578).
2. ~~trust-vc emits bundles from verification context.~~ ✅ `emit_merge_bundle()` static extraction bridge (#2595).
3. Trust needs a production consumer plus parity coverage for that bundle (tracked downstream).
4. After that gate lands, wire trust-vc's proof surface into Trust as its proof backend (alongside trust-mc/trust-wp).

**End state:** Trust = one unified verifier (MIR/exec + borrows + model checking + separation logic + proof calculus) over a single ay solver, emitting checkable proof certificates. "Independently checkable" is the destination, not today's state: closing the kernel's NIA/BV/Array/Seq trust gap is Workstream B.1 of `docs/ROADMAP.md`.

## Success Metrics

Canonical status snapshot: recount from the sources named in `CLAUDE.md`
("Where the numbers live") — `evals/verus/verus-tests.json` for the corpus
manifest and `docs/replacement-progress.md` for the running ledger. (The former
`scripts/vision_scorecard.py` / `reports/vision-scorecard-current.md` pair no
longer exists in this repo.)

### Achieved Tracked Surface (Tier 0)

These rows describe project feature milestones, not upstream Verus corpus
acceptance. Replacement status is governed by the internal replacement roadmap and
the generated evidence report.

| Metric | Status |
|--------|--------|
| `#[proof]` basic | ✅ Non-recursive proof functions verify |
| `#[decreases]` basic + when/via | ✅ Termination proofs with fuel encoding |
| `Seq`/`Set`/`Map` | ✅ Comprehensive ghost collections with ay array encoding |
| ay end-to-end | ✅ ~5,800 tests across 6 crates, 8/8 VerifyThis practice |
| Broadcast/triggers | ✅ Quantified auto-applied lemmas with E-matching |
| VerifyThis 8/8 | ✅ Equality reconciliation + ay revert (#2386, closed) |
| Reveal/Hide/Opaque | ✅ `#[opaque]` + `reveal!()` + `reveal_group!()` + inline spec (#1901, #2488 closed) |
| Datatype encoding | ✅ Option/Result UF + recursive ADTs + Multiset (#1942, #2421, #2484 closed) |
| Polymorphism | ✅ Poly/Box/Unbox type erasure + roundtrip axioms (#2053 closed) |
| Trait verification | ✅ Trait method UF + postcondition axioms (#2425 closed) |
| Mutable references | ✅ SSA shadow rewrite + place-based reasoning (#2426, #2515 closed) |
| MergeBundle v4 | ✅ v4 schema + emission bridge + merge-runner rendering (#2403, #2578, #2595, #2596) |
| calc!/assert_forall_by | ✅ Calculational proofs + quantified assertions (#2413, #2416 closed) |
| Struct invariants | ✅ Type-level invariants via type_invariant (#2419 closed) |
| Tracked\<T\> | ✅ Linear/affine ghost ownership (#2427 closed) |
| Mutual recursion | ✅ Full SCC-based termination via Tarjan (#2054 closed) |
| Recursive type well-formedness | ✅ AcceptRecursiveType checking (#2484 closed) |
| Chained comparisons | ✅ `a <= b <= c` lowered to conjunction (#2493 closed) |
| Multiset\<T\> | ✅ Spec collection with 12 encoder tests (#2421 closed) |
| Per-function rlimit | ✅ `#[trust_vc::rlimit(N)]` solver timeout override (#2489 closed) |
| Error expansion | ✅ Assertion splitting for localized diagnostics (#2485 closed) |
| Recommends clause | ✅ Soft precondition warnings for spec functions (#2483 closed) |
| assert_by_compute | ✅ Symbolic proof-by-computation interpreter (#2454 closed) |
| Higher-order combinators | ✅ fold/filter/map/flat_map for Seq, Set, Map (#2466 closed) |
| Inline spec functions | ✅ Body substitution for non-opaque specs (#2488 closed) |
| Loop invariant inference | ✅ Auto-infer `for i in range` invariants (#2502 closed) |
| Auto trigger inference | ✅ Automatic trigger selection for quantifiers (#2461 closed) |
| SMT pruning | ✅ Remove unreachable SMT declarations (#2520 closed) |
| Real number arithmetic | ✅ `RealArithOp`, Int-to-Real/Real-to-Int casts (#2517 closed) |
| Systematic overflow checking | ✅ `OverflowBehavior`/`Div0Behavior`/`BitshiftBehavior` tracking (#2516 closed) |
| Place-based reasoning | ✅ `Place`/`PlaceX` memory location reasoning (#2515 closed) |
| Prophecy variables | ✅ Future-value reasoning via `Proph<T>` ghost type (#2519 closed) |
| Code health | ✅ 500-line violations resolved, thread-local consolidated (#2522, #2481 closed) |
| Soundness audit closure | ✅ All 14 sub-issues closed (#1840 closed) |
| Static proof extraction | ✅ `StaticProofContext` → `MergeBundle` emission bridge (#2593, #2595) |

### Merge Readiness
| Metric | Target |
|--------|--------|
| MergeBundle consumer in trust-mc | trust-mc production path imports and executes trust_vc MergeBundle v4 (#1994 closed). trust-vc-side work complete; replacement evidence remains separate. |
| SortMeta parity | ✅ SortMeta covers all encoder sorts including FloatingPoint and collections (#2693 closed). |

### v2: Beyond Verus

| Priority | Capability | Status | Tracking | Notes |
|----------|------------|--------|----------|-------|
| **P1** | Incremental solving (push/pop) | done | #2648 | Measurement issue confirmed the push/pop path is already landed |
| **P1** | Parallel function verification | done | #2647 | Per-function ay instances landed |
| **P2** | Counterexample extraction to source | done | #2651 | Map solver models back to source-level names |
| **P1** | VC-level caching | done | #2646 | Skip re-verification of unchanged functions |
| **P2** | Per-assertion SMT pruning | done | #2649 | Tighten the quantifier universe per query |
| **P2** | Proof failure localization | done (follow-up: #2682) | #2652 | Basic implementation done; fast-path gap filed as P1 #2682 |
| **P2** | UNSAT proof certificates | done | #2654 | Resolution traces from ay, re-checked by trust-vc-kernel; NIA/BV/Array/Seq lemmas still accepted on trust |
| **P2** | Adaptive E-matching depth | done | #2665, #2720, #2742 | Shipped as the `EMATCHING_ESCALATION_BUDGETS` retry ladder + `set_ematching_round_limit` (`encoder/verification/assertion.rs:1290-1470`) |
| **P3** | Demand-driven cross-function inlining | done | #2655 | Inline callees when contracts are too weak |

#### v2.1: Native Theory Adoption

ay provides native theory solvers that trust_vc's encoder now adopts.

| Priority | Capability | Status | Tracking | Notes |
|----------|------------|--------|----------|-------|
| **P2** | IEEE floating-point verification | done | #2680 Slice 1 | `Float{32,64}` → native `Sort::FloatingPoint` via ay-fp |
| **P2** | Native sequence theory | landed, opt-in | #2680 Slice 2 | `Seq<T>` → native `Sort::Seq(T)` via ay's `ay-seq` theory solver (`encoder/collection_seq_native/`); behind the `native-seq` feature, which is NOT in `default` |
| **P3** | Native string theory | landed, opt-in | #2680 Slice 3 | `String` → `Sort::String` via ay-strings (word equations); behind the `native-strings` feature, which is NOT in `default` |
| **P2** | Merge-contract sort parity | done | #2693 | SortMeta now covers FloatingPoint and collection sorts |

#### Deferred research

| Priority | Capability | Why it matters |
|----------|------------|----------------|
| **P3** | Proof-guided quantifier instantiation | Feedback loop between verifier and solver |

Verification-aware optimization hints left this table: they SHIPPED as
`cargo trust-vc check --emit-hints`
(`crates/cargo-trust-vc/src/emit_hints.rs`, `llvm_hints.rs`,
`optimization_pipeline.rs`).

## Scope Boundaries

### In Scope (v1 tracked surface)
- Broad Verus-style proof attribute and macro coverage (count the
  `#[proc_macro*]` items in `crates/trust-vc/src/lib.rs` rather than quoting a
  number here); replacement proof requires the evidence gate.
- Ghost collections with full higher-order combinators
- Trait verification, polymorphism, mutable references
- Recursive termination, broadcast lemmas, SMT pruning

### In Scope (v2 — NEXT)
- Performance: incremental solving, parallelism, VC-level caching, per-assertion pruning
- Usability: counterexamples, proof failure localization
- Solver capabilities: proof certificates, adaptive E-matching retries, demand-driven body inlining
- Native theories (v2.1): IEEE FP verification, native Seq/String via ay theory solvers (#2680; Seq/String are opt-in features, not defaults)

### Deferred Research (not in active v2 lane)
- Proof-guided quantifier instantiation

### Out of Scope (other Trust capabilities or other tools)

These belong to sibling capabilities within Trust, or to other tools — not to the
trust-vc proof backend:

- **TY/protocol verification** → strategically belongs in Trust's model-checking
  capability (trust-mc) or tRust. trust-vc still carries a feature-gated
  experimental bridge for compatibility and internal testing, but this is not
  part of the v1/v2 roadmap.
- **NN verification** → ny (different math: abstract interpretation, not SMT)
- **Separation logic** → Trust's trust-wp capability
- **Model checking (BMC, k-induction)** → Trust's trust-mc capability
- **Z3 compatibility** → we use ay exclusively
