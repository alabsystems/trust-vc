# trust-vc v1.0

trust-vc is the **proof-calculus and SMT backend of Trust** (the Trust rustc
fork), where it lives as the `first-party/trust-vc` submodule.
Its destination is to be Trust's proof backend: it consumes Trust's compiler IR
(`trust-ir`), discharges proof obligations on the pure-Rust **ay** SMT solver
(no Z3, ay is git-pinned), and emits independently-checkable proof certificates
back to Trust.

**R1 (2026-07-11) retired the Verus-surface program — and was AMENDED two days
later.** `docs/capability-audit-2026-07-13.md` §preamble reinstates the program
in two phases, and the **ACTIVE GOAL** (author-set 2026-07-15, re-affirmed
2026-07-18) is **100% of Verus functionality in trust-vc at "full or
superior"** — verification-power parity on the native surface across the whole
156-file corpus, per `docs/execution-plan-100-verus-2026-07-15.md` §2/§5.
Phase 1: all of Verus's verification functionality on a better, ay/Trust-native
surface (no slavish copying; diagnostic-string byte-parity stays retired).
Phase 2 (follow-up): drop-in Verus replacement, scoped in that doc's §8.
R1 was a documentation-only change — it deleted no macro, no CLI, no driver:
the 69-macro frontend, targo-trust-vc (invoked `targo trust-vc`;
`cargo trust-vc` alias), and `trust-vc-driver` are retained Phase-2 assets,
not debt. Per the ratified two-language spec-surface design (the Trust repo's
`docs/design/2026-07-09-two-language-spec-surface.md` §6, §3.2), Trust still
ships **one** spec surface (first-class Rust contract clauses + Clean) and
engines stay invisible backends behind trust-router.
What trust-vc **is**: the fleet's auto-active SMT proof-calculus engine
(triggers, fuel, broadcast, `calc!`, `by(compute)`) — trust-vc-core +
trust-vc-trust-engine + trust-vc-types behind the router, with the ay-native
collection theory encodings and the production `mir_memory` certificate lane.
The 156-file Verus corpus is retained forever as regression material, re-keyed
to the native Trust surface at R4; the evidence gate is the corpus-port
instrument that measures the active goal.

> North-star design: see `design-trust-proof-backend.md` (Trust proof
> backend). `design-rustc-driver-frontend.md` (the Verus-compat front
> end) is historical — superseded at R1.

**Author:** Andrew Yates <andrewyates.name@gmail.com> · **Version:** 1.0.0 · **License:** Apache-2.0
**Copyright:** 2026 Andrew Yates

## What trust-vc Does

trust-vc proves mathematical properties of Rust code — preconditions, postconditions, loop invariants, termination measures, quantifiers — automatically, using the ay SMT solver. As Trust's proof backend it lowers resolved compiler facts (types/borrows from `trust-ir`) into its own typed IR, discharges them through ay, and re-checks ay's UNSAT/Alethe proofs to produce certificates Trust can trust. Users reach it through Trust's native contract surface via trust-router — the trust-vc-specific annotation dialect is not a user-facing surface (R1 as amended: the native surface is primary; the macro frontend is a retained Phase-2 compat asset).

```rust
use trust_vc::*;

#[trust_vc::proof]
fn lemma_double_positive(x: u64) {
    trust_vc::requires!(x > 0);
    trust_vc::ensures!(x + x > x);
    // ay proves: for all x > 0, x + x > x (under bitvector arithmetic)
}

#[trust_vc::proof]
#[trust_vc::decreases(n)]
fn lemma_sum_nonneg(n: u64) {
    if n > 0 {
        lemma_sum_nonneg(n - 1);  // recursive example; self-recursion verified via fuel encoding
    }
    trust_vc::assert!(sum(n) >= 0);
}
```

When you run `targo --unverified test`, trust_vc collects proof obligations from your annotations and sends them to ay. Each assertion is checked via refutation: ay attempts to find a counterexample to `NOT(assertion)`. If no counterexample exists (UNSAT), the assertion is verified. If ay finds one, it reports the concrete values that violate the property. `--unverified` describes the outer Trust compiler lane; these trust_vc engine checks still run.

## How It Works

### Architecture

```
crates/
├── cargo-trust-vc/         # CLI wrapper, package `targo-trust-vc` (`targo trust-vc check`; `cargo trust-vc check` alias)
├── trust-vc/               # Proc macros (#[proof], #[decreases], requires!, etc.)
├── trust-vc-core/          # Verification engine (encoder, VC generation, ay interface)
├── trust-vc-driver/        # rustc-driver (THIR) front end — the one crate needing the Trust rustc fork
├── trust-vc-kernel/        # Proof certificate wire format + independent resolution checker
├── trust-vc-merge-contract/# Versioned MergeBundle boundary for Trust integration
├── trust-vc-merge-runner/  # Merge parity gate runner
├── trust-vc-oracle/        # LLM proof oracle — semantic counterexample feedback
├── trust-vc-std/           # Standard-library lemma surface for specifications
├── trust-vc-trust-engine/  # Trust adapter: consumes trust-ir compiler facts, emits proof certificates
└── trust-vc-types/         # Ghost types (Seq, Set, Map) for specifications
```

### Verification Pipeline

```
Annotated Rust code
    │
    ▼
Proc macros expand annotations        (trust-vc/src/lib.rs)
    │
    ▼
Obligation collection via              (trust-vc-core/src/verify_macro.rs)
thread-local context
    │
    ▼
Rust expressions lowered to trust-vcExpr (trust-vc-core/src/ir_lowering/)
typed IR and encoded to ay terms
    │
    ▼
AYEncoder encodes obligations:         (trust-vc-core/src/encoder/)
  - Declare variables with correct
    sorts (i32→BV32, u64→BV64, etc.)
  - Add assumptions as constraints
  - For each assertion: check SAT(¬P)
    │
    ├─ UNSAT  → Verified ✓
    ├─ SAT    → Counterexample (model extracted)
    └─ Unknown → solver limit reached
```

### Three Compilation Modes

Each proc macro generates code for three `cfg` targets:

| Mode | When | Behavior |
|------|------|----------|
| `cfg(test)` | `targo --unverified test` | Collects obligations, invokes ay, panics on counterexample |
| `cfg(trust_mc)` | trust-mc verifier | Emits `__trust_vc_*` marker variables for trust-mc to consume |
| default | `targo --unverified build` | Proof functions become no-ops; assertions become runtime panics |

### What ay Encodes

The encoder (`encoder/`) handles:

- **Bitvector arithmetic** — i8/u8 through i128/u128 with correct width and signedness
- **Boolean logic** — &&, ||, !, with proper short-circuit semantics
- **Comparisons** — signed and unsigned variants selected per-expression
- **Type casts** — widening (sign/zero extend), narrowing (extract), signed↔unsigned
- **Collections** — `Seq<T>` as `Array(BV64, T)`, `Set<T>` as `Array(T, Bool)`, `Map<K,V>` as `Array(K, V)`
- **Quantifiers** — `forall!` and `exists!` with trigger patterns
- **Match expressions** — compiled to chained if-then-else
- **Function calls** — recursive functions as uninterpreted functions with decrease checks
- **Division safety** — literal division by zero rejected during encoding; variable divisors checked via SMT

Solver limits: 30s timeout / 128MB term-memory per assertion (overridable via `#[rlimit]`). BV-mode queries use a 10s thread watchdog since ay-dpll's BV solver bypasses internal timeout. Extended retry uses 20s for marginal BV timeouts (#2313).

The in-tree performance proof and regression-gate coverage is maintained in
the internal engineering notes that are not shipped in the public mirror.

## Features

The tables below highlight the common user-facing surface. The fuller exported
proc-macro inventory lives in `crates/trust-vc/src/lib.rs`.

### Common Proof Annotations

| Annotation | Purpose |
|-----------|---------|
| `#[trust_vc::proof]` | Mark function as a proof (ghost code, erased at runtime) |
| `#[trust_vc::spec]` | Specification function (pure, for use in contracts) |
| `#[trust_vc::decreases(expr)]` | Termination measure for recursive functions |
| `#[trust_vc::broadcast]` | Lemma auto-applied as background axiom |
| `#[trust_vc::trigger(pattern)]` | SMT trigger for quantifier instantiation |
| `#[trust_vc::external_body]` | Trust boundary — body not verified |
| `#[trust_vc::opaque]` | Hide a spec function body until explicitly revealed |
| `#[trust_vc::inline]` | Substitute a non-opaque spec function body at the call site |
| `#[trust_vc::returns(name)]` | Named return value for use in `ensures!` |
| `#[trust_vc::contract(...)]` | Combined attribute for `requires` / `ensures` / `returns` / `decreases` |

### Common Verification Macros

| Macro | Purpose |
|-------|---------|
| `trust_vc::requires!(P)` | Precondition — assumed true on entry |
| `trust_vc::ensures!(P)` | Postcondition — verified on exit |
| `trust_vc::assert!(P)` | Proof assertion — verified at point of use |
| `trust_vc::assume!(P)` | Axiom — assumed without proof |
| `trust_vc::invariant!(P)` | Loop invariant — checked inductively |
| `trust_vc::invariant_except_break!(P)` | Loop invariant — checked inductively but not assumed after `break` |
| `trust_vc::loop_ensures!(P)` | Loop postcondition — required on normal loop exit |
| `trust_vc::loop_decreases!(expr)` | Loop termination measure — must decrease each iteration |
| `trust_vc::forall!(\|x: T\| P)` | Universal quantifier |
| `trust_vc::exists!(\|x: T\| P)` | Existential quantifier |
| `trust_vc::choose!(\|x: T\| P)` | Witness extraction from an existential predicate |
| `trust_vc::old!(expr)` | Pre-state snapshot for postconditions |
| `trust_vc::proof_block!({ ... })` | Inline proof block in executable code |
| `trust_vc::assert_by!(P, { proof })` | Assert P with scoped proof |
| `trust_vc::assert_by_contradiction!(P, { proof })` | Prove `P` by deriving contradiction from `!P` |
| `trust_vc::calc! { ... }` | Calculational proof chain; each step must justify the next |
| `trust_vc::extern_spec!(fn ...)` | Attach contracts to external functions |
| `trust_vc::reveal!(fn_name)` | Reveal an opaque spec function in the current proof |
| `trust_vc::broadcast_use!(group)` | Selectively activate a broadcast group inside a proof |
| `trust_vc::arbitrary!(T)` | Introduce an unconstrained symbolic value of type `T` |
| `trust_vc::closure!(...)` | Closure literal with verification contracts |

### Legacy Experimental Protocol Surface

| Annotation | Purpose |
|-----------|---------|
| `#[trust_vc::protocol]` | TY protocol state machine declaration |
| `#[trust_vc::action]` | TY next-state action declaration |
| `#[trust_vc::safety]` | TY safety invariant declaration |
| `#[trust_vc::liveness]` | TY liveness property declaration |

Feature-gated behind `ty`. This bridge remains in trust_vc for compatibility
and internal experiments, but protocol verification is not part of the active
trust_vc roadmap; strategic ownership lives in `trust-mc` / `tRust`.

### Ghost Types (trust-vc-types)

Specification-only collection types. These are `PhantomData` wrappers — zero runtime cost, used only in proof context.

| Type | ay Encoding | Key Operations |
|------|-------------|----------------|
| `Seq<T>` | `Array(BV64, T)` | `len()`, `index()`, `push()`, `subrange()` |
| `Set<T>` | `Array(T, Bool)` | `contains()`, `insert()`, `remove()`, `union()`, `intersect()` |
| `Map<K,V>` | `Array(K, V)` | `get()`, `insert()`, `contains_key()`, `dom()` |
| `Ghost<T>` | unwrapped `T` | `view()` — extract ghost value in spec context |
| `Multiset<T>` | `Array(T, BV64)` | `count()`, `insert()`, `remove()`, `union()`, `intersect()` |
| `Tracked<T>` | unwrapped `T` | Linear/affine ghost ownership for proof mode |
| `Proph<T>` | unwrapped `T` | Prophecy variables for future-value reasoning in proof mode |
| `List<T>` | UF datatype (Nil/Cons) | Recursive linked list for structural induction |
| `Tree<T>` | UF datatype (Leaf/Branch) | Recursive binary tree for structural induction |
| `Snapshot<T>` | unwrapped `T` | Captures value at program point for postconditions |
| `SpecFn<Args, Ret>` | uninterpreted function | Spec-only closures for higher-order specifications |
| `LocalInvariant<K,V,Pred>` | tracked ghost state | Local invariant wrapper for open/close reasoning |

## Current Status

**Build:** passes `targo --unverified check --workspace --all-targets` in this checkout. **Verus replacement:** evidence-gated by
`./target/debug/targo-trust-vc evidence` (the `cargo-trust-vc` bin remains as a back-compat alias); **`replacement_verdict: not_proven`** today — not proven until the full trust-vc,
upstream Verus, and corpus gates pass from a clean worktree. **Honest parity:** the feature surface below is broad, but only
~12–15% of the upstream Verus test corpus is genuinely ported at the proof-language level (111 of 156 entries are
`unsupported-gap`). Do not read "broad feature list" as Verus parity; the gate is the source of truth. The dependency-ordered
path to a proven replacement lives in the internal parity-to-100 program plan. **Lines:** about
727k Rust across 11 workspace crates (source + tests). **Note:** there is
**no CI** — every gate is a local script (`scripts/quality_audit.py`,
`scripts/stock-harness.sh`, the merge-parity gate) run by hand, so test health
is not gate-enforced; run `targo --unverified test` locally before relying on a checkout.

### Replacement Evidence

Generate the current replacement evidence report:

```bash
./target/debug/targo-trust-vc evidence . --strict --run-trust-vc --run-trust-vc-corpus --run-verus \
  --verus-path /path/to/verus --verus-rev <verus-commit> \
  --manifest evals/verus/verus-tests.json --json --markdown
```

The command exits `0` only when every required gate passes. It exits `1` and
writes a `not_proven` report when evidence is incomplete, including manifest-only
runs, missing upstream Verus enumeration, unclassified tests, unsupported gaps,
dirty worktrees, stale ay pins, or failed trust-vc/Verus test commands.
The JSON and Markdown reports expose accepted executable ports separately from
unsupported-gap evidence: accepted ports include owner issues, trust-vc paths,
expected cases, source hashes, obligation fingerprints, and proof-gap status
that must remain empty; unsupported entries may list partial cases, but those
cases do not count toward a replacement claim.

### Feature Highlights

Where these go beyond Verus: trust-vc emits **independently-checkable proof
certificates** (ay UNSAT/Alethe proofs re-checked by `trust-vc-kernel`), whereas
Verus trusts a black-box Z3 with no checkable artifact; it rides **native ay
decision procedures** (Seq/Set/Map/Multiset/String/FP/BV) that sidestep Z3's
MBQI/quantifier fragility; it uses **no Z3** (pure-Rust, reproducible); and as
Trust's proof backend it contributes to one unified verifier (MIR/exec +
borrows + model checking + separation logic + proof calculus, one engine, one
solver) rather than a Rust-surface-plus-Z3 silo. It also offers cross-IR
portability and an ay-vs-Z3 differential oracle.

- Broad proc macro surface (69 macros) with three-way cfg expansion (test/trust-mc/runtime)
- End-to-end verification: annotation → obligation collection → ay solving → result
- Bitvector-precise arithmetic for all Rust integer types (i8–i128, u8–u128)
- Pre/postconditions, loop invariants, proof functions, recursive termination (self + mutual via Tarjan SCC)
- Quantifiers (forall/exists) with automatic trigger inference
- Ghost collections (Seq, Set, Map, Multiset) with higher-order combinators (fold, filter, map, flat_map)
- Datatype encoding (Option/Result, recursive ADTs), polymorphism (Poly/Box/Unbox), trait verification
- Mutable reference verification via SSA shadow rewriting
- Place-based reasoning for memory locations
- Mode-aware overflow/division/shift checking (OverflowBehavior/Div0Behavior/BitshiftBehavior)
- Real number arithmetic, nondeterministic expressions, prophecy variables
- Broadcast lemmas, reveal/hide/opaque, inline spec functions, SMT pruning
- calc!, assert_by, assert_by_contradiction, assert_by_compute, choose
- Proof-call postcondition propagation (ensures assumed at call site)
- Loop invariant auto-inference for `for i in range` loops
- Per-function rlimit, recommends clauses, extern specs
- Specialized solver modes: nonlinear arithmetic, bitvector, compute
- SMT reachability pruning to reduce solver load
- Compile-fail tests via trybuild, 300+ integration test files

### Roadmap: Verus Parity, then Trust's Proof Backend

The near-term milestone is evidence-gated Verus replacement/compatibility (the
parity benchmark). The destination is serving as Trust's proof backend, where
the capabilities below — independently-checkable certificates, incremental
solving, parallel verification, source-level counterexamples — feed Trust's
unified verifier rather than a standalone tool.

| Priority | Capability | Status | Tracking |
|----------|------------|--------|----------|
| **P1** | Incremental solving (push/pop reuse) | done | #2648 |
| **P1** | Parallel function verification | done | #2647 |
| **P2** | Counterexample extraction to source level | done | #2651 |
| **P1** | VC-level caching | done | #2646 |
| **P2** | Per-assertion SMT pruning | done | #2649 |
| **P2** | Proof failure localization | done | #2652 |
| **P2** | UNSAT proof certificates from ay | done | #2654 |
| **P2** | Adaptive E-matching depth | deferred | #2665 |
| **P3** | Demand-driven cross-function inlining | done | #2655 |

Execution enablers such as test-tiering, gate-serialization removal, and the
`targo trust-vc` wrapper are tracked in epic #2656 rather than this public
capability table.

#### Deferred research

- **P3** Custom sequence theory solver in ay
- **P3** Verification-aware optimization hints
- **P3** Proof-guided quantifier instantiation

### Trust integration

- **Trust backend integration** — trust_vc ships MergeBundle v4 for ingest into Trust's unified verifier; downstream adoption is tracked outside the replacement proof gates.

## Dependencies

| Crate | Purpose |
|-------|---------|
| `ay-core` | SMT types and term AST |
| `ay-dpll` | DPLL(T) solver engine (includes array, EUF, BV, LRA, NIA theories) |
| `ay-frontend` | SMT-LIB2 parsing for merge-runner |
| `syn` | Rust AST parsing for proc macro expression translation |

All ay crates are pinned to exact git revisions. trust-vc does not depend on Z3
or any external/third-party SMT solver. "Pure Rust" refers to the solver
*algorithms*: the dependency closure is not C-free. The ay lock graph includes
GMP/MPFR/libc crates (`gmp-mpfr-sys`, `rug`, `libc`) through its arithmetic and
resource-measurement backends, and `ay-dpll`'s default `jit` feature pulls in
`ay-jit`, a self-hosted native-code JIT that emits and executes machine code
(`mmap`/`PROT_EXEC`, `extern "C"` function pointers). These are part of the
trusted computing base.

## Integration Path

trust-vc integrates as Trust's proof backend. Verus-style proofs (trust-vc),
separation logic (trust-wp), and model checking (trust-mc) are capabilities
*within* Trust — one unified verifier over one solver (ay), not separate
end-products:

```
trust_vc (Verus-style proofs) ──┐
                              ├──► Trust (unified verifier) ──► proof certificates
trust_wp (separation logic) ────┘    (trust-mc / trust-wp / trust-vc capabilities)
```

Current integration staging:

1. trust_vc exports a versioned `MergeBundle` boundary via `trust-vc-merge-contract`.
2. Trust must add a production consumer for that bundle and pass parity coverage through that ingest path.
3. Only after that ingest/parity gate exists do the trust_vc capabilities land inside Trust's unified verifier.

## Installation and Usage

```bash
targo --unverified build
targo --unverified test
```

Targo requires an explicit lane. These commands build and test trust_vc without
claiming that the Trust compiler verified the produced artifacts. Use
`targo trust check` for the compiler-verified lane.

### `trust-vc` — verify in one command

The build produces two front ends over the same verifier (both from crate
`targo-trust-vc`). Neither needs cargo, rustc, a sysroot or an external solver
at runtime: sources are parsed with `syn` and the proof obligations are
discharged in-process on `ay`.

```bash
trust-vc example > demo.rs   # a tiny annotated program that verifies as-is
trust-vc demo.rs             # verify a single file
trust-vc path/to/crate       # verify a crate through its src/ tree
trust-vc --help              # answers with nothing installed, as does --version
```

Every check flag is reachable from either front end — `--function`, `--filter`,
`--json`, `--ci`, `--diff`, `--localize`, `--no-cheating`, `--timeout`, `-j`,
`--emit-certificate`, `--emit-hints`, `--watch` — and the cargo subcommand is
unchanged:

```bash
targo trust-vc check <crate>   # `cargo trust-vc check <crate>` still works (alias)
```

Cargo-driven selection (`--package`, `--manifest-path`, `--features`, …) stays
on the cargo subcommand. `trust-vc` never silently ignores a flag: it names the
one you passed and the one to use instead.

## Running proofs on STOCK rustc (no Trust fork — minutes, not hours)

The trust-vc verification **engine** (`trust-vc-core` + the `trust_vc` proc
macros + the `ay` SMT solver crates) has **no `rustc_private` dependency and no
`#![feature(...)]`**: `verify_function_from_file` parses the proof fixture itself
and runs the AY engine + trust-vc-kernel — all pure Rust. Only the separate
`trust-vc-driver` rustc-driver links `rustc_private` and needs the Trust
rustc-fork stage2 (an hours-long build). The native-deductive proof harness does
**not** use the driver, so it builds and runs on stock/homebrew rustc in well
under a minute (cold build ≈ 50s here).

Use the committed runner — it handles the stock-rustc flag override for you:

```bash
# Curated AY real-fixture suite (eval/optimum/incumbent/composite/verdict-chain):
scripts/stock-harness.sh

# A single proof target (any tests/ay_*_realbody.rs etc.):
scripts/stock-harness.sh ay_incumbent_vig_realbody
```

Equivalently, by hand:

```bash
RUSTC=/opt/homebrew/bin/rustc RUSTFLAGS="" /opt/homebrew/bin/cargo test \
  -p trust-vc-core --test ay_incumbent_vig_realbody --locked
```

Both overrides leave the Trust-toolchain path untouched:

`RUSTC` matters because homebrew `cargo` — a non-rustup cargo that itself
ignores `rust-toolchain.toml`'s `channel = "trust"` — still resolves `rustc`
from `PATH`, where the rustup shim usually shadows homebrew's; the shim honors
the `trust` pin and fails whenever that toolchain is absent or mid-rebuild.
Pinning `RUSTC` to the rustc that ships with the chosen cargo keeps both
halves of the toolchain stock. `RUSTFLAGS=""` clears any ambient Trust-only
`-Z` flags that stock rustc would reject (the committed `.cargo/config.toml`
no longer sets `build.rustflags`; Targo injects its own per-unit off-switch).
Dependencies stay on the same exact revisions recorded in `Cargo.lock`; the
stock harness does not redirect them to mutable local checkouts.

If you drive a rustup `stable` instead, `cargo +stable` (or
`RUSTUP_TOOLCHAIN=stable`) handles both halves at once.
`scripts/stock-harness.sh` selects the homebrew cargo automatically and
isolates artifacts in `target-stock/` so it never thrashes the
Trust-toolchain `target/` cache.

## False-Verified Fuzzing

The cargo-fuzz suite for contradictory postconditions lives under
`fuzz/` and exercises the VC extraction plus encoder path.

```bash
targo --unverified test --manifest-path fuzz/Cargo.toml
```

For a 1-hour release sweep, run each target for 15 minutes:

```bash
rustup run nightly cargo fuzz run ensures_false -- -max_total_time=900
rustup run nightly cargo fuzz run strict_inequality -- -max_total_time=900
rustup run nightly cargo fuzz run mode_crossing -- -max_total_time=900
rustup run nightly cargo fuzz run collections_contradiction -- -max_total_time=900
```

Extended fuzzing runbooks stay in the internal development docs; the public
mirror keeps the executable fuzz targets and commands above.

## Documentation

The public mirror ships the crate sources, examples, and tests. The broader
engineering deep dives stay in the private development repo. Those internal
notes cover:

- Verus parity tracking and follow-on roadmap
- Unsigned overflow semantics
- ay backend architecture
- Verification idioms and proof patterns
- Termination encoding and `#[decreases]` semantics
- Rust-to-ay type mapping
- `__trust_vc_*` metadata for trust-mc integration

## License

Apache 2.0. Copyright 2026 Andrew Yates
