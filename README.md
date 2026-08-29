# trust-vc v0.3

trust-vc is the **proof-calculus and SMT backend of Trust** (the Trust rustc
fork), where it lives as the `first-party/trust-vc` submodule. It consumes
Trust's compiler IR (`trust-ir`), discharges proof obligations on the pure-Rust
**ay** SMT solver (no Z3; ay is pinned by exact git revision), and emits proof
certificates back to Trust.

Inside Trust the front end is `trust-vc-trust-engine`, which consumes `trust-ir`
requests carrying resolved compiler facts (types/borrows); Trust ships one spec
surface (first-class Rust contract clauses plus Clean) with engines as invisible
backends. The `trust_vc::*` annotation dialect documented below is trust-vc's
*own* surface — what the standalone `trust-vc` command reads and what the
Verus-compatibility driver targets. The 156-file Verus corpus under
`evals/verus/` is retained as regression material; the `evidence` gate below
measures parity against it.

> North-star design: `design-trust-proof-backend.md` (Trust proof backend).
> `design-rustc-driver-frontend.md` (the Verus-compat front end) is
> historical — superseded at R1 (2026-07-11).

**Author:** Andrew Yates <andrewyates.name@gmail.com> · **Version:** 0.4.0 · **License:** Apache-2.0
**Copyright:** 2026 Andrew Yates

## What trust-vc Does

trust-vc proves mathematical properties of Rust code automatically —
preconditions, postconditions, loop invariants, termination measures,
quantifiers. This is the program `trust-vc example` prints; it verifies as-is:

```rust
/// Returns `x + 1`, proven greater than `x` when `x < u32::MAX`.
#[trust_vc::contract(
    requires(x < u32::MAX),
    ensures(ret > x),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}
```

Each assertion is checked by refutation: ay attempts to find a counterexample to
`NOT(assertion)`. UNSAT means verified; SAT means ay reports the concrete values
that violate the property. Delete the `requires` line above and the proof fails
with `x = 4294967295`.

## How It Works

### Architecture

```
crates/
├── cargo-trust-vc/         # CLI, package `targo-trust-vc` — builds both the `trust-vc`
│                           #   and `cargo-trust-vc` bins
├── trust-vc/               # Proc macros (#[proof], #[decreases], requires!, etc.)
├── trust-vc-core/          # Verification engine (encoder, VC generation, ay interface)
├── trust-vc-driver/        # Typed lowering seam + rustc-driver (THIR) Verus-compat front
│                           #   end — the one crate needing the Trust rustc fork
├── trust-vc-kernel/        # Proof certificate wire format + independent resolution checker
├── trust-vc-merge-contract/# Versioned MergeBundle boundary for Trust integration
├── trust-vc-merge-runner/  # Merge parity gate runner
├── trust-vc-oracle/        # LLM proof oracle — semantic counterexample feedback
├── trust-vc-std/           # Standard-library lemma surface for specifications
├── trust-vc-trust-engine/  # Trust adapter: consumes trust-ir compiler facts
└── trust-vc-types/         # Ghost types (Seq, Set, Map) for specifications
```

### Verification Pipeline

```
Annotated Rust code
    │
    ▼
Proc macros expand annotations         (trust-vc/src/lib.rs)
    │
    ▼
Obligation collection via              (trust-vc-core/src/verify_macro.rs)
thread-local context
    │
    ▼
Rust expressions lowered to            (trust-vc-core/src/ir_lowering/)
`TrustVcExpr` typed IR
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
    └─ Unknown → budget exhausted (fails closed)
```

### Compilation Modes

Each proc macro generates code for four `cfg` lanes, which are mutually
exclusive:

| Mode | When | Behavior |
|------|------|----------|
| `cfg(test)` | `targo --unverified test` | Collects obligations, invokes ay, panics on counterexample |
| `cfg(trust_mc)` | trust-mc verifier | Emits `__trust_vc_*` marker variables for trust-mc to consume |
| `cfg(trust_vc_driver)` | `trust-vc-driver` | Emits `trust_vc_core::__driver_markers::*` surface-bridge calls |
| default | `targo --unverified build` | Proof functions become no-ops; assertions become runtime panics |

### What ay Encodes

The encoder (`encoder/`) handles:

- **Bitvector arithmetic** — i8/u8 through i128/u128 with correct width and signedness
- **Boolean logic** — &&, ||, !, with proper short-circuit semantics
- **Comparisons** — signed and unsigned variants selected per-expression
- **Type casts** — widening (sign/zero extend), narrowing (extract), signed↔unsigned
- **Collections** — `Seq<T>` as `Array(BV<usize>, T)`, `Set<T>` as `Array(T, Bool)`,
  `Map<K,V>` as `Array(K, V)`, `Multiset<T>` as `Array(T, Int)`
- **Quantifiers** — `forall!` and `exists!` with trigger patterns
- **Match expressions** — compiled to chained if-then-else
- **Function calls** — recursive functions as uninterpreted functions with decrease checks
- **Division safety** — literal division by zero rejected during encoding; variable divisors checked via SMT

Per-solve budgets are **deterministic work first, wall clock only as a liveness
backstop**, and both fail closed — exhausting either yields `Unknown`, never
`Verified`:

- 400,000-conflict deterministic budget, overridable per function with
  `#[verifier::rlimit(N)]`;
- 30s wall-clock backstop (a quantified solve gets a wider far-out watchdog —
  130s with the defaults);
- 60s thread watchdog on ground bit-blasted BV queries, because ay-dpll's BV
  solver is not interruptible; a marginal BV timeout is retried once at 2×;
- 512MB process memory limit. A per-encoder term-memory cap is opt-in via
  `TRUST_VC_TERM_MEMORY_MB`.

## Features

The tables below highlight the common user-facing surface. The full 69-macro
inventory lives in `crates/trust-vc/src/lib.rs`.

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

`#[trust_vc::protocol]`, `#[trust_vc::action]`, `#[trust_vc::safety]` and
`#[trust_vc::liveness]` are a legacy experimental bridge to TY protocol state
machines. The macros always compile; the model-checking backend is behind the
`ty` feature. Protocol verification is not on the active trust-vc roadmap —
strategic ownership lives in `trust-mc` / `tRust`.

### Ghost Types (trust-vc-types)

Specification-only types, used only in proof context. The collection wrappers
are zero-sized `PhantomData` markers; `List`/`Tree` are real enums used for
structural induction.

| Type | ay Encoding | Key Operations |
|------|-------------|----------------|
| `Seq<T>` | `Array(BV<usize>, T)` | `len()`, `index()`, `push()`, `subrange()` |
| `Set<T>` | `Array(T, Bool)` | `contains()`, `insert()`, `remove()`, `union()`, `intersect()` |
| `Map<K,V>` | `Array(K, V)` | `get()`, `insert()`, `contains_key()`, `dom()` |
| `Multiset<T>` | `Array(T, Int)` | `count()`, `insert()`, `remove()`, `union()`, `intersect()` |
| `Ghost<T>` | unwrapped `T` | `view()` — extract ghost value in spec context |
| `Tracked<T>` | unwrapped `T` | Linear/affine ghost ownership for proof mode |
| `Proph<T>` | unwrapped `T` | Prophecy variables for future-value reasoning in proof mode |
| `List<T>` | UF datatype (Nil/Cons) | Recursive linked list for structural induction |
| `Tree<T>` | UF datatype (Leaf/Branch) | Recursive binary tree for structural induction |
| `Snapshot<T>` | unwrapped `T` | Captures value at program point for postconditions |
| `SpecFn<Args, Ret>` | uninterpreted function | Spec-only closures for higher-order specifications |
| `LocalInvariant<K,V,Pred>` | tracked ghost state | Local invariant wrapper for open/close reasoning |

## Current Status

**Verus replacement: not proven.** `evals/verus/verus-tests.json` pins 156
upstream Verus test files — **46 `ported`, 106 `unsupported-gap`, 4
`not-applicable`**. `unsupported-gap` is a failing classification under the
manifest's own gate, so `replacement_verdict` is `not_proven` and stays that way
until every entry is `ported` or `not-applicable` *and* the full trust-vc,
upstream-Verus and corpus gates pass from a clean worktree. The feature tables
above describe **in-repo surface, not corpus acceptance** — do not read a broad
feature list as Verus parity. The gate is the source of truth.

**Scale.** About 922k lines of Rust across the 11 workspace crates (source and
tests), including 900+ integration test files and compile-fail tests via
trybuild.

**No CI.** There is no `.github/workflows`; every gate is local.
`targo trust-vc gate` runs fmt, clippy, test, examples, evidence triage and a
fuzz smoke in one command; `scripts/quality_audit.py`, `scripts/stock-harness.sh`
and `scripts/merge_parity_gate.py` run individually. Test health is therefore not
enforced on push — run the gate locally before relying on a checkout.

### Replacement Evidence

Generate the current replacement evidence report:

```bash
./target/debug/targo-trust-vc evidence . --strict --run-trust_vc --run-trust-vc-corpus --run-verus \
  --verus-path /path/to/verus --verus-rev <verus-commit> \
  --manifest evals/verus/verus-tests.json --json --markdown
```

Exit `0` only when every required gate passes; otherwise exit `1` and write a
`not_proven` report — manifest-only runs, missing upstream Verus enumeration,
unclassified tests, unsupported gaps, dirty worktrees, stale ay pins, and failed
trust-vc/Verus test commands all block. The reports keep accepted executable
ports (with owner issue, trust-vc path, expected cases, source hash, obligation
fingerprint, and a proof-gap status that must be empty) separate from
unsupported-gap evidence, whose partial cases never count toward a replacement
claim.

### Feature Highlights

**Checkable proof certificates.** Under the `proof-certificates` feature, ay's
UNSAT resolution trace is re-checked by `trust-vc-kernel`: an independent
propositional resolution checker, plus structural validation of EUF
(transitivity/congruence) and LRA (Farkas) theory lemmas. Lemmas from theories
the kernel does not yet check — **NIA, BV, Array, Seq — are accepted on trust**
and are part of the trusted computing base. Certificates export to JSON, binary,
Alethe, DRAT, and Lean5 proof terms.

**No Z3.** The solver is the pure-Rust `ay` stack, pinned by exact git revision.
No external or third-party SMT solver is invoked at build time or at run time.

**Native ay theories.** Set/Multiset/Map subset obligations lower to ay's native
`set.subset` / `multiset.subset` / `map.subset` atoms rather than a quantified
array encoding, so they decide without MBQI. ay's native `Seq` and `String`
sorts are wired behind the opt-in `native-seq` / `native-strings` features; the
default encodings are arrays.

Engine surface:

- 69 proc macros with four-way cfg expansion (test / trust-mc / driver / runtime)
- End-to-end verification: annotation → obligation collection → ay solving → result
- Bitvector-precise arithmetic for all Rust integer types (i8–i128, u8–u128)
- Pre/postconditions, loop invariants, proof functions, recursive termination (self + mutual via Tarjan SCC)
- Quantifiers (forall/exists) with automatic trigger inference and adaptive E-matching escalation
- Ghost collections (Seq, Set, Map, Multiset) with higher-order combinators (fold, filter, map, flat_map)
- Datatype encoding (Option/Result, recursive ADTs), polymorphism (Poly/Box/Unbox), trait verification
- Mutable reference verification via SSA shadow rewriting; place-based reasoning for memory locations
- Mode-aware overflow/division/shift checking (OverflowBehavior/Div0Behavior/BitshiftBehavior)
- Real number arithmetic, nondeterministic expressions, prophecy variables
- Broadcast lemmas, reveal/hide/opaque, inline spec functions; calc!, assert_by,
  assert_by_contradiction, assert_by_compute, choose
- Proof-call postcondition propagation, loop invariant auto-inference for
  `for i in range`, per-function rlimit, recommends clauses, extern specs
- Specialized solver modes: nonlinear arithmetic, bitvector, compute
- Incremental solving (push/pop reuse), VC-level caching, parallel function
  verification, per-assertion SMT reachability pruning, source-level
  counterexamples, proof-failure localization, demand-driven cross-function
  inlining, optimization hints from proven facts (`--emit-hints`)

Deferred research: proof-guided quantifier instantiation.

### Trust integration

`trust-vc-merge-contract` exports **MergeBundle v4**, the versioned boundary for
ingest into Trust's unified verifier. `trust-vc-trust-engine` accepts three
`trust-ir` request modes: `ImportProofCertificates`, `MergeProofCertificates`,
and `DischargeProofObligations`. The first two are wired.
`DischargeProofObligations` is **not yet answerable** — nothing in the engine
lowers a `trust-ir` function body to trust-vc's IR, so such a request fails
loudly rather than silently reading as success. `mir_memory` is the typed
MIR memory/ownership facade Trust lowers into.

Downstream adoption inside Trust is tracked outside this repo's gates.

## Dependencies

| Crate | Purpose |
|-------|---------|
| `ay-core` | SMT types and term AST |
| `ay-dpll` | DPLL(T) solver engine (array, EUF, BV, LRA, NIA, Seq, Set, Map, Multiset, String, FP theories) |
| `ay-frontend` | SMT-LIB2 parsing for merge-runner |
| `ay-sys` | OS boundary: memory measurement and process supervision |
| `trust-ir` | Trust's compiler IR — the request/facts protocol |
| `syn` | Rust AST parsing for proc macro expression translation |

All ay crates are pinned to exact git revisions. trust-vc does not depend on Z3
or any external SMT solver, and arbitrary-precision arithmetic runs on pure-Rust
`num-bigint`. "Pure Rust" refers to the solver *algorithms*: the dependency
closure is not C-free. `ay-sys` links `libc`/`windows-sys` for memory
measurement and process supervision, and `ay-dpll`'s default `jit` feature pulls
in `ay-jit`, a self-hosted native-code JIT that emits and executes machine code
(`mmap`/`PROT_EXEC`, `extern "C"` function pointers). These are part of the
trusted computing base.

## Installation and Usage

```bash
targo --unverified build
targo --unverified test
```

Targo requires an explicit lane. These commands build and test trust_vc without
claiming that the Trust compiler verified the produced artifacts. Use
`targo trust check` for the compiler-verified lane.

### `trust-vc` — verify in one command

The build produces two front ends over the same verifier, both from crate
`targo-trust-vc`. Neither needs cargo, rustc, a sysroot or an external solver at
runtime: sources are parsed with `syn` and the proof obligations are discharged
in-process on `ay`.

```bash
trust-vc example > demo.rs   # a tiny annotated program that verifies as-is
trust-vc demo.rs             # verify a single file
trust-vc path/to/crate       # verify a crate through its src/ tree
trust-vc new --bin myproj    # scaffold a crate wired the same way
trust-vc --help              # answers with nothing installed, as does --version
```

Every check flag is reachable from either front end — `--function`, `--filter`,
`--json`, `--ci`, `--diff`, `--localize`, `--no-cheating`, `--timeout`, `-j`,
`--emit-certificate`, `--emit-hints`, `--emit-hints-json`, `--watch`, `-v` — and
the cargo subcommand is unchanged:

```bash
targo trust-vc check <crate>   # `cargo trust-vc check <crate>` still works (alias)
```

Subcommands: `check`, `gate`, `fuzz`, `evidence`, `suggest`, `new`,
`verus-compat`. Cargo-driven selection (`--package`, `--manifest-path`,
`--features`, …) stays on the cargo subcommand. `trust-vc` never silently
ignores a flag: it names the one you passed and the one to use instead.

## Running proofs on STOCK rustc (no Trust fork — minutes, not hours)

The trust-vc verification **engine** (`trust-vc-core` + the `trust_vc` proc
macros + the `ay` SMT solver crates) has **no `rustc_private` dependency and no
`#![feature(...)]`**: `verify_function_from_file` parses the proof fixture itself
and runs the AY engine + trust-vc-kernel, all pure Rust. Only the separate
`trust-vc-driver` rustc-driver links `rustc_private` and needs the Trust
rustc-fork stage2 (an hours-long build). The native-deductive proof harness does
**not** use the driver, so it builds and runs on stock/homebrew rustc in well
under a minute.

Use the committed runner — it handles the stock-rustc flag override for you:

```bash
scripts/stock-harness.sh                       # curated AY real-fixture suite
scripts/stock-harness.sh --all                 # every ay_* native-proof driver
scripts/stock-harness.sh ay_incumbent_vig_realbody   # one proof target
```

Equivalently, by hand:

```bash
RUSTC=/opt/homebrew/bin/rustc RUSTFLAGS="" /opt/homebrew/bin/cargo test \
  -p trust-vc-core --test ay_incumbent_vig_realbody --locked
```

Both overrides leave the Trust-toolchain path untouched. `RUSTC` matters because
homebrew `cargo` ignores `rust-toolchain.toml`'s `channel = "trust"` but still
resolves `rustc` from `PATH`, where the rustup shim — which honors that pin, and
fails whenever the toolchain is absent or mid-rebuild — usually shadows
homebrew's. `RUSTFLAGS=""` clears ambient Trust-only `-Z` flags that stock rustc
would reject (the committed `.cargo/config.toml` no longer sets
`build.rustflags`; Targo injects its own per-unit off-switch). Dependencies stay
on the exact revisions in `Cargo.lock` — no redirect to mutable local checkouts.
On a rustup `stable`, `cargo +stable` (or `RUSTUP_TOOLCHAIN=stable`) handles both
halves at once. The script picks the homebrew cargo automatically and isolates
artifacts in `target-stock/`.

## False-Verified Fuzzing

The cargo-fuzz suite for contradictory postconditions lives under `fuzz/` and
exercises the VC extraction plus encoder path. Targets: `ensures_false`,
`strict_inequality`, `mode_crossing`, `collections_contradiction`.

```bash
targo trust-vc fuzz                     # every target, 30s each (needs cargo-fuzz)
targo trust-vc fuzz ensures_false --time 900
targo --unverified test --manifest-path fuzz/Cargo.toml   # the targets' own tests
```

## Documentation

The public mirror ships the crate sources, examples, tests, the eval corpus, and
the root `design-*.md` documents. The broader engineering deep dives — Verus
parity tracking, ay backend architecture, verification idioms, termination
encoding, Rust-to-ay type mapping, `__trust_vc_*` metadata for trust-mc
integration — stay in the private development repo.

## License

Apache 2.0. Copyright 2026 Andrew Yates
