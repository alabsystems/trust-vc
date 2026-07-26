# Hardening trust-vc via Trust — and improving the Trust toolchain to lift trust-vc

> Written 2026-06-22 after building trust-vc against the **latest Trust toolchain**
> (`rustc 1.96.0-dev (57daf265f 2026-06-22)`, the self-hosted stage2 Trust build)
> with **all sibling deps bumped to latest**: ay `ba8c0d18 → 59eb4a778d` (+340,
> absolute HEAD), ty `e2a6f8c4 → 7d1d4635`, trust-ir `5e1e8d1 → 9ff0269`. This doc records the
> build discoveries, their corrections, and a grounded plan. Companion to
> `design-trust-proof-backend.md` (north star), `design-rustc-driver-frontend.md`
> (front-end), and `grand-strategy-ay.md` (solver / Problem B).

## 0. What the bump empirically proved

The Trust toolchain is now a **verifying compiler**: it runs ay-backed Trust-MIR
verification inline on *every* crate it compiles, including ordinary crates.io
dependencies. Building trust-vc against it surfaced four classes of discovery:

| # | Discovery | Severity | Correction |
|---|-----------|----------|------------|
| D1 | `trustc` verification-by-default hard-errors on a *guaranteed* Level-0 safety violation in `proc-macro2` (`self.source_text[byte_range]`), and ICEs (`normalize_erasing_regions`) on `serde_core` — for **dependency** crates cargo builds with `--cap-lints allow`, which the verification layer does **not** honor. | Blocks any `cargo build` with deps | `-Zno-trust-verify` (Rust-compat mode; compiler-suggested). Baked into local `.cargo/config.toml`. |
| D2 | The bumped `trust-ir` moved its ~330-symbol verification-request/bundle re-export behind a new default-on `request-reexports` feature; trust-vc consumes it with `default-features = false`, so `trust_ir::NativeVerificationBundle` etc. vanished → `trust-vc-trust-engine` fails to compile. | Blocks build | Re-enable the (zero-dep) feature on the workspace `trust-ir` dep. Committed. |
| D3 | Bumping ay +338 commits regressed **7** trust-vc-core capabilities from a decided verdict to fail-closed `Unknown(incomplete)` (div/mod reconstruction identity; array→slice alias ×2; `Seq::new` OOB index; `Seq::update` bounds ×2; mutual-recursion defining axiom). Fail-closed = **safe**, but a real capability loss. | Behavioral regression | Triaged per-cluster (§3); fix locus = ay vs trust-vc encoding. |
| D4 | The same bump made ay **prove** the true nonlinear-real lemma `real_nonlinear2` (`a≥0∧b≥0∧a²+b²==(ab+1)q ⟹ q≥0`) in Default mode **without** the `by(nonlinear_arith)` hint — a **sound completeness gain** in ay that **diverges from Verus's Z3 incompleteness**. | Parity-divergence design call | §3.4 — superset vs exact-parity decision. |

**Headline:** the bump compiles cleanly after D1/D2, but it is **not a Pareto
improvement** — it trades 7 completeness regressions for many soundness fixes and
at least one completeness gain. Trust's own superproject pins ay only **3 commits
behind** the HEAD trust-vc now uses (those 3 are PB/totalizer internals), so
**Trust integrates the same regressed ay** — D3 is an ay-quality issue shared by
the whole stack, not trust-vc pinning too bleeding-edge.

The deepest lesson: **trust-vc's own ~16k-test suite is not run in CI** (no
`.github/workflows` in this checkout; ROADMAP Workstream A.1 already flags it).
Every discovery above would have been caught automatically by a CI that builds
on the Trust channel and runs `cargo test`. That single gap is why a 9-test
behavioral regression could ship silently.

---

## 1. Corrections applied (2026-06-22)

**Committed (portable):**
- `Cargo.toml`: ay pin `ba8c0d18 → 4e0a0538` (all four crates, common rev); add
  `features = ["request-reexports"]` to the `trust-ir` dep. `Cargo.lock` updated.

**Local-only (NOT committed — machine-specific build setup):**
- `.cargo/config.toml`: `[patch]` redirect of ay/ty/trust-ir to the sibling
  checkouts (corrected the stale `ssh://` URL to the `https://` dep source), and
  `rustflags = ["-Zno-trust-verify"]`. These belong to the local working tree by
  design (the local working-notes doc keeps the patch block uncommented).

---

## 2. Hardening trust-vc *using Trust* (consume facts, don't reconstruct them)

The single biggest robustness lever is already half-built and under-exploited.

### 2.1 Make the trust-ir bundle path the primary front end (retire the syn re-parser for *reading*)
`trustc` already lowers THIR → `trust_ir::Module`, walks `TyCtxt`/MIR to build
typed `TrustContractBundle`, and emits `trust_ir::ProofObligation` +
`NativeVerificationBundle` (`trust/crates/{trust-thir-lower,trust-mir-extract,
trust-ir-bridge}`). `trust-vc-trust-engine::native_trust_ir_bundle` already
consumes these end-to-end through the existing `VerificationContext`/encoder/ay/
kernel pipeline — **bypassing the 311-file `syn` re-parser entirely**, and it
verifies through ay in tests today.

This dissolves the dominant parity blocker (the "front-end information ceiling":
trust-vc's `syn` parser round-trips types through strings and *erases* `&T`/`&mut
T`; `extract_type_string` → `ir_type_parse`). The design memo
`design-rustc-driver-frontend.md` proposes rebuilding a THIR→IR lowering and
**never references this already-working path** — the two should be reconciled:
- Promote the bundle path to trust-vc's primary *reading* surface for
  compiler-driven runs; keep the `syn` DSL as the *authoring* surface
  (`#[proof]`/`requires!`/`ensures!`). End state per the design:
  *syn = how specs are written; Trust/trust-ir = how programs are read; ay+kernel
  = how they are proved and certified.*
- Scope the in-tree `rustc_driver` (its THIR lowering is currently an
  unconditional `UnsupportedContract` stub) down to **only** the borrow/exec MIR
  facts not yet in the bundle, instead of a full parallel lowering.
- Wire `cargo trust-vc` / the evidence gate to accept a `NativeVerificationBundle`
  input so corpus files verify from `trustc`-emitted facts.

### 2.2 Actually *lower* compiler facts (not just presence-check them)
Today the engine validates ownership/borrow/lifetime/alias/provenance facts for
non-emptiness only (`lib.rs` ownership preflight; `trust_ir_adapter.rs`), and the
driver's frame capability takes a *caller-supplied* modified-set rather than
decoding a real `NativeCompilerFacts` payload. Harden by lowering
`TrustOwnershipContext` + per-obligation `NativeObligationSource.facts` into
`TrustVcExpr` assumptions / frame VCs, so frame & alias obligations are **proved
from the compiler write-footprint** — a soundness property Verus (Rust-surface
specs) structurally cannot match. This is design Needed-item #1.

### 2.3 Independently recompute the module digest (close an unchecked-input hole)
`native_trust_ir_bundle.rs` recomputes the compiler-facts and certificate digests
but trusts the producer-supplied `trust_ir_module_digest` **verbatim**. The new
`trust_ir::Module::stable_digest()` (commit 9ff0269, now reachable post-bump) lets
trust-vc recompute it from the bytes and reject on mismatch — symmetric with the
existing recomputes, re-establishing the trust-ir→trust-vc lowering anchor from
data rather than a label.

### 2.4 Cross-check the version boundary at build time
Three independently hand-maintained schema versions exist:
`NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION = 4` (trust-ir, exact-match),
`TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION = 1` (trust-vc), and
`trust.spec-predicate.v1` (Trust). They are not cross-checked, and trust-vc pins
trust-ir by `branch = main` (a moving target — exactly how D2 slipped in). Harden:
pin trust-ir to an exact rev/tag, add a compile-time assertion that trust-vc's
expected bundle schema version equals the trust-ir constant, and consider a single
negotiated handshake surfaced in the bundle.

### 2.5 Consume translation-validation + adopt the serializable proof bundle
- `trust-ir-contract` now ships `TranslationCheck`/`RefinementVc` records. Consume
  them to **independently re-derive** trust-vc's own lowering refinement
  (source→target point + formula per `CheckKind`) and assert it matches what was
  discharged — a self-check that lowering preserved source semantics.
- ay now exports a producer-independent `SerializableProofBundle`
  (`export_last_unsat_bundle` / `re_check_bundle_strict` / `PROOF_BUNDLE_SCHEMA`,
  commit b34bef3466). Adopt it as trust-vc's certificate format and wire
  `re_check_bundle_strict` into `cargo trust-vc evidence`, so every "Verified" is
  re-checked by code that never trusted the producing solver — the headline
  soundness edge over Verus's black-box Z3, made real and version-fail-closed.

---

## 3. Correcting the bump's behavioral regressions (D3/D4)

> Per the gate-integrity rule: **do not slacken a test to mask a regression.**
> Each below is classified by fix locus; tests are updated only where the new ay
> verdict is genuinely correct (a sound completeness change), never to hide a lost
> capability.

**Cross-cutting verdict (adversarially verified).** All 7 regressions are
**fail-closed** (a decided verdict became `Unknown`/lost a counterexample — the
*safe* direction; no over-proving, no fabricated model, no trust-vc unsoundness,
no trust-vc source bug). Their fix locus is **ay-side**: they are the
over-conservative cost of ay's own *soundness-hardening* commits in the bump
window. The bump correctly traded some completeness for more soundness; recovery
is ay-side completeness work, guarded by §4.3.

**Resolution status (2026-06-23): 3 of 9 addressed soundly + verified; 6 remain
(one coherent program). trust-vc-core lib: 16277 pass / 6 fail (was 9).**
- **§3.1 div/mod (1)** — ✅ FIXED at root in ay (shared `(q,r)`), verified, no
  over-proving, ay's own suite green.
- **§3.4 nonlinear (2)** — ✅ RESOLVED as sound completeness gains (one test
  flipped to `Verified`, one retargeted to a still-undecidable goal). No masking:
  the lemma is provably valid + non-vacuous.
- **§3.2 array/seq + §3.3 mutual-recursion (6)** — REMAIN: all are the same deep
  **SAT-with-quantifiers model-validation** gap (ay returns `sat` but
  `model_validated:false` on `forall`-premised queries → trust-vc soundly demotes
  to `Unknown`). Precisely diagnosed with standalone repros; left tracked, **not
  masked**. Fixing them is the Problem-B SAT-counterexample-under-quantifiers
  program (ay-side model validation, or trust-vc broadcast-revalidation
  extension) — not a one-shot, and entangled with ay's soundness gates, so not
  attempted blindly.

> An earlier speculative `eval_array` concrete-def-preference fix (sound; passed
> ay's 288 array tests) did not move these — confirming the failing direction is
> SAT-model-validation, not the UNSAT/`eval_array` path; it was reverted to keep
> ay pristine. (§3.2 carries the corrected diagnosis.)

### 3.1 div/mod reconstruction `(a/3)*3 + a%3 == a` (1 test) — ✅ FIXED (ay)
**Root cause (evidence-driven):** ay's constant-divisor elimination
(`mod_div_elim/mod.rs` `rewrite_mod`/`rewrite_div`) minted **independent** fresh
`(q, r)` pairs for the SAME `(dividend, k)`, so `(div a 3)` and `(mod a 3)` got
unlinked vars and the Euclidean identity `a = 3·(div a 3) + (mod a 3)` was only
derivable via a uniqueness deduction the LIA layer left as `unknown` (spinning
72 s on the standalone repro). **Fix:** share one canonical `(q, r)` per
`(dividend, k)` so the defining constraint `a = k·q + r ∧ 0 ≤ r < |k|` is emitted
once and links them directly. Provably sound (both ops denote the unique
Euclidean pair; same models, emitted once) and shorter recursion. Also taught
the Alethe proof rewriter (`proof_rewrite_division.rs`) the new `_divmod_*`
witness names and updated the share-constraints count test (6→3; its own comment
flagged this as "could be optimized"). **Verified:** standalone query now
`unsat` (was 72 s `unknown`); probes confirm no over-proving (a deliberately
false divisor-5 identity stays `sat`); ay `mod_div` 26/0, `proof_rewrite` 10/0,
`proof` 24/0, `division` 18/0; trust-vc-core `euclidean` test passes (9→8).
Symbolic-divisor div/mod kept fail-closed (untouched).

### 3.2 array→slice / `Seq::new` / `Seq::update` + §3.3 mutual-recursion (6 tests) — KNOWN-OPEN ay `arrayext + quantifier` bug cluster
**Definitive diagnosis (fully evidence-driven; supersedes both the `eval_array`
and the "batch vs in-process" attributions, which were artifacts — see below).**
These obligations carry an array-extensionality `forall`
(`∀ idx. select(sl,idx)==select(ar,idx) ∨ ¬(idx<len)`). On the **faithful** query
ay returns `unknown(incomplete)` — and crucially it **still** does so even when
the model is fully pinned (`assert (= sl ar)` + `len = 3`): ay cannot discharge
the quantified array-extensionality consequence
`(sl=ar) ⟹ ∀idx. select(sl,idx)==select(ar,idx)`. The bump's new (sound)
**strict model-validation gate** (`pipeline.rs::apply_strict_model_gate`,
`verify_model_strict` → `DefinitiveEval`) then correctly degrades the incomplete
candidate to `Unknown(Incomplete)` rather than reporting a false SAT. **This is
exactly the cluster the latest ay's own soundness hunt lists as confirmed-OPEN**:
`alia_pointwise_forall_arrayext_neg_polarity_false_unsat` /
`alia_quant_arrayext_polarity_false_unsat`
(`ay/reports/2026-06-22-soundness-hunt-confirmed-bugs.md`; repros in
`benchmarks/smt/regression/soundness_fuzz_blitz/`). So the 6 trust-vc regressions
are the trust-vc manifestation of a **known-open, deep ay array-ext + quantifier
reasoning gap** the ay maintainer is already tracking — not a trust-vc bug, and
not weaken-the-gate territory (weakening it reintroduces the false-SAT the bump
fixed). Pre-bump, ay reported these as false-SAT (invalid models) and trust-vc
emitted counterexamples whose *conclusions* were coincidentally correct; the bump
made ay honestly sound here and exposed the underlying completeness gap.
- **ay fix (the real one):** close the `arrayext + quantifier` reasoning gap —
  derive `select` equalities from array equality under quantifiers and/or proper
  MBQI model completion for the pointwise-equality `forall`. This is the open ay
  soundness/completeness work (`grand-strategy-ay.md` B-track); deep, must be
  verified against ay's full array+quantifier suite to avoid re-introducing
  false-SAT. A faithful standalone repro now exists (derived from the dumped VC).
- **sound interim mitigation (trust-vc):** the `native-seq` encoding (decidable
  `Seq(T)`, no two-array `forall`) sidesteps the cluster — a feature-flag, not a
  gate change.

> **Two methodology corrections worth keeping.** (1) My earlier "batch ay returns
> `sat`" was an artifact: `Solver::to_smtlib2()` **omits the fresh
> `__trust_vc_len_idx_*` declarations** it references, so the CLI dropped the
> erroring assertions and solved a *weaker* query (spurious `sat`). With the
> missing declaration restored, batch and in-process agree (`unknown`). **This is
> a real ay `to_smtlib2` serialization bug** (incomplete declaration emission)
> that would also make kernel certificate re-checks unfaithful — worth fixing
> independently. (2) The `eval_array` concrete-def-preference idea was sound but
> not the cause (it's the UNSAT/model-eval path; this is quantifier discharge).

### 3.3 mutual-recursion defining axiom refutation (1 test) — ay-completeness-regression
Confirmed real (the false postcondition `count_down_b(0) == 1` previously
produced a `Counterexample`, now `Unknown(Incompleteness)`). Attribution is
contested between ay `35616352ab` (the new strict `apply_strict_model_gate` /
`IteDefinitionOracle` definitive-false model gate that can suppress a genuine
ite+UF counterexample model) and the quantifier-instantiation/forall-refutation
series earlier in the window. `Counterexample → Unknown` is the **safe**
direction (trust-vc maps `Incompleteness` to a model-less failure downstream).
- **ay fix:** enforce the ite-definition equality in the EUF+LIA (Nelson-Oppen)
  combiner so the UF-app value is forced consistent with the selected `ite`
  branch *before* model construction — then the real counterexample survives the
  definitive-false gate.

### 3.4 D4 — nonlinear-real now verifies without the hint (2 tests) — ✅ RESOLVED (sound gain)
The lemma is **valid** (negation UNSAT) and the premise **satisfiable** (not
vacuous) — both confirmed standalone — so ay's `Verified` is **sound**: its NRA
got complete enough to discharge `real_nonlinear2` in Default mode. This makes
trust-vc a **superset** of Verus on this input (Verus's Z3 needs the
`by(nonlinear_arith)` hint), fully consistent with the stated goal ("*proven full
replacement (superset) of Verus*"). **Resolution (the superset choice):**
- `test_nonlinear_real_division_lemma_now_verifies_without_hint` — flipped to
  expect `Verified` (records the sound Default-mode NRA gain).
- `test_incompleteness_split_nonlinear_real_is_modelless_failure` — **retargeted**
  from `real_nonlinear2` (no longer incomplete) to the AM-GM inequality
  `x*x + y*y >= 2*x*y`, which ay still genuinely cannot decide without a
  sum-of-squares certificate (confirmed `unknown` standalone) — so it keeps
  honestly pinning the incompleteness→model-less-failure machinery rather than a
  since-closed gap.
- Open follow-up (corpus gate, not these unit tests): ensure
  `cargo trust-vc evidence` treats "trust-vc proves more than Verus" as a pass,
  not a divergence (a superset replacement must).

---

## 4. Improving the *Trust toolchain* to improve trust-vc

These are toolchain-side changes whose payoff lands in trust-vc (and, because they
share ay, in `trustc`'s inline verifier too — fix once, lift both).

### 4.1 trustc: make verification honor `--cap-lints allow` (D1, durable fix)
The workaround is a blunt global `-Zno-trust-verify`. The correct fix is for the
verification layer to **respect `--cap-lints allow`** the way the lint layer does:
a dependency crate built with capped lints should have its Trust verification
findings capped (downgraded to warn/off), not turned into hard errors. Add a
`-Ztrust-verify-target=<crate>` default keyed to the primary crate so deps and
build scripts skip verification automatically under cargo (the flag already
exists; wire it to the cargo "primary package" signal). Until then a committed
`rustflags = ["-Zno-trust-verify"]` (or per-crate scoping) is the trust-vc policy.

### 4.2 trustc: fix the `serde_core` `normalize_erasing_regions` ICE
The verification pass forces normalization of a nested projection
(`Iterator::Item` inside `Pair::Second`) that vanilla lowering defers, panicking in
`rustc_middle/.../normalize_erasing_regions.rs:171`. `-Zno-trust-verify` masks it;
the fork should `try_normalize_erasing_regions` on the verification path (the panic
message itself suggests this). File against the Trust compiler with the serde_core
repro.

### 4.3 ay: guard against completeness regressions (D3 root program)
The 338-commit bump silently regressed div/mod, array/slice, seq, and
quantifier-instantiation completeness on shapes trust-vc relies on. Build the
**differential-completeness guard** from `grand-strategy-ay.md` #2:
- A corpus of "ay must DECIDE this" queries (the exact shapes behind the 7
  regressions + the broader trust-vc obligation corpus), run as an ay-side gate so
  a future ay change that turns a decided query into `Unknown` **fails ay's CI**,
  not trust-vc's months later.
- Pin trust-vc's ay to an **exact rev that Trust integrates** (align with the
  superproject's `first-party/ay` pin), not raw `branch`/HEAD, so the inline
  verifier and trust-vc share one vetted ay and bumps are deliberate + co-tested.

### 4.4 ay: finish native theories to retire trust-vc's hand-rolled quantified axioms
trust-vc carries ~40 encoder files asserting `forall`/length/cardinality axioms
(MBQI-fragile; the project itself flags `MAX_MBQI_ROUNDS=5` and "out-of-fragment
SAT/UNSAT = critical soundness bug"). Each axiom is trusted background theory — the
largest hand-written-axiom blast radius in the engine. Finishing ay-native QF
decision procedures (Set card/subset ✓ landed; Map read-through; Multiset count;
Seq higher-order/comprehension carrier — the `OUT_OF_FRAGMENT_OPS` fail-closed in
`set/src/lib.rs`) lets trust-vc **delete** the foralls and reason decidably. This
is the #1 lever in the grand strategy and directly shrinks the soundness surface.

### 4.5 ay + kernel: close the certificate gap so every "Verified" is checkable
The independent kernel still accepts BV/Array/Seq/NIA lemmas "on trust." Closing
that gap (kernel checks the new `SerializableProofBundle` for those theories) makes
*every* in-Trust "Verified" independently certifiable — the v2 differentiator that
is only possible because we own the solver.

---

## 5. Soundness hardening internal to trust-vc (surfaced by review)

- **`encoder/diagnostics.rs::is_demoting`** is the central hand-curated soundness
  gate: 5 of 6 encoding approximations (`BoundsCheckSkipped`, `IntBvCoercion`,
  `BroadcastCapHit`, `ForallSkolemization`, `GroundFixpointNonConvergence`) are
  marked **non-demoting** — a `Verified` is emitted to the user even when the
  approximation fired — with no co-located soundness argument. Add a one-line
  justification per variant and a discriminating test per non-demoting category (a
  goal that verifies *only* because the approximation fired must be caught). Invert
  to fail-closed for any approximation whose safety can't be argued.
- **Unknown-variant tripwire:** the `Incompleteness` vs `SolverUnknown` split
  (`unknown_category.rs`) fail-opens new ay-dpll `UnknownReason` variants to
  `SolverUnknown` via a wildcard. Keep the wildcard, but add a CI tripwire that
  enumerates ay's variants and fails when a new one is unmapped (the D3 bump added
  exactly such variants — e.g. `Unknown(Incomplete)` from the Violated→Unknown
  degrade). Property-test that no Resource/Timeout reason reaches
  `is_incompleteness() == true`.
- **Route A (Int-sorted collection lengths):** replace the fixed-width-BV
  "concat length no overflow" obligation with Int-sorted lengths across ~43 sites
  (the pattern is already implemented for native-strings/seq in the same file,
  gated by features; it needs no front-end data). A genuine Phase-0 soundness item
  achievable on the syn path today; Route B (`assume bvadd(l,k) ≥ l`) was unsound
  and reverted — keep the near-MAX vacuity regression tests.

---

## 6. Sequencing (dependency-ordered)

1. **CI on the Trust channel** running `cargo build` (`-Zno-trust-verify`) +
   `cargo test --workspace` + `cargo trust-vc evidence --port-manifest-only`.
   This is the cheapest, highest-leverage item and would have caught D1–D4. (ROADMAP A.1.)
2. **Resolve D3/D4** per §3 (triage verdicts): ay-side regressions → ay
   differential-completeness guard + fix; trust-vc-side → encoding adaptation;
   D4 → superset decision. Re-green the suite *honestly*.
3. **Pin discipline** (§2.4 + §4.3): exact ay/trust-ir revs aligned with the Trust
   superproject; build-time schema cross-check.
4. **Module-digest recompute (§2.3)** + **serializable proof bundle adoption (§2.5/§4.5)**
   — low-effort soundness wins now reachable post-bump.
5. **Compiler-fact lowering completeness (§2.2)** then **bundle path as primary
   front end (§2.1)** — the dominant parity unlock; reconcile with the rustc-driver memo.
6. **ay native theories (§4.4)** in parallel — retire the hand-rolled quantified
   axioms; close the `is_demoting` soundness arguments (§5) alongside.
