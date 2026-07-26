# Design: migrate datatype encoding to ay's native `Sort::Datatype`

**Status:** P0–P2 LANDED + green (2026-06-05). P3 (opportunistic collection-file
promotions via corpus refresh) PENDING. Authored 2026-06-05.

**Update (P0–P2 done):** carrier chosen as `Sort::Uninterpreted(name)` (==
`Sort::Datatype(dt).as_term_sort()`, ay's term-level datatype sort) — this kept the
cascade bounded (consumers' `Sort` pattern-matching unchanged; real cascade confined to the
size/invariant UFs + one hard-coded `Sort::Int` selector domain in `place_encoding.rs`).
Tester symbol is `is-{ctor}` (ay hard-codes the hyphen in `try_declare_datatype` + the mbqi
recognizers; there is no ay knob, and ay must not be edited). `datatype_axioms.rs` deleted;
`try_declare_datatype` now populates ay's native registry so the mbqi tester-completion
recognizers fire and symbolic datatype obligations discharge natively (the witness class).
One real completeness regression surfaced + was fixed *in the engine* (not the test):
datatype-valued **match results** are `ite` trees, and ay's native theory resolves a
selector/tester only on a syntactic constructor leaf or a datatype variable — NOT through an
`ite` tree. `match_encode::bind_datatype_match_result` re-establishes the link soundly by
asserting, per tester/selector `f`, the unconditional ground equation
`f(m) == distribute_unary_over_ite(f, match_term)` (`f(ite(c,a,b))==ite(c,f(a),f(b))` is a
tautology; constructor-leaf eval is the native axiom). Full lib 16097/0; manifest untouched;
no promotion (foundational capability, prerequisite for the collection files).
**Owner threads it unblocks:** #2779 (collection files), symbolic-self trait verification (#2785/#2425).
**This is a design/scoping artifact, not a verified increment — it changes no proof, no manifest, no count.**

## Problem

trust-vc encodes user datatypes (structs/enums, and builtins like `Option`/`Result`)
as **hand-rolled uninterpreted-function symbols over `Sort::Int`** — see
`encoder/datatype.rs::register_datatype` (`carrier_sort = Sort::Int`, line ~93) plus the
quantified soundness axioms in `encoder/datatype_axioms.rs` (exhaustiveness, per-variant
tester, selector roundtrip, injectivity, disjointness).

When a datatype value appears **symbolically** in a main-path obligation — i.e. a function
parameter / `self` that is never constructed in-scope, so no constructor term exists to
e-match — ay leaves the **exhaustiveness forall** (`forall x:Int. is_A(x) ∨ … ∨ is_N(x)`)
and the **per-variant tester forall** (`forall x. is_V(ctor(x))`) "skipped" during SAT-side
model validation (`../ay ay-dpll executor/model/validation/observation.rs` →
`ValidationSkipKind::Quantifier`). `mbqi_soundness_gate_for_skipped_quantifiers`
(`../ay ay-dpll executor/mbqi.rs:336`) then degrades the otherwise-SAT model to
`Unknown(QuantifierEmatchingExistsIncomplete)`.

Net effect: any obligation whose discharge needs SAT-side model construction over a symbolic
datatype value returns Unknown. This is **fail-closed (not a soundness hole** — the conforming
witness still VERIFIES on the UNSAT side; only the SAT side is degraded), but it blocks:
- 8+ collection files (`seqs`, `sets`, `multiset`, `slices`, `vec`, `std`, `hash`, `btree` — all
  `#2779`, all backed by view datatypes),
- symbolic-self trait-method result reasoning (`let v = c.get(); assert(v==5)` over `c: Counter`).

Proven (2026-06-05, firsthand bisection) that **no sound trust-vc-only reshape** of the
hand-rolled axioms defuses this: triggers are irrelevant to the soundness gate; the
`is_V(x)=true` constant-UF-definition shape is collapsed by ay `mk_eq` `(= x true) -> x`; and
ay's boolean-tester completion recognizers (`mbqi.rs:988-1018`
`is_true_datatype_tester_instance` / `is_single_constructor_datatype_tester_instance`) require
ay's **native** datatype registry (`is_constructor` / `datatype_iter`), which the UF-over-Int
encoding never populates. See memory `reference_requires_discharge_campaign` for the full proof.

## Why native datatypes fix it (no ay change required)

ay already ships a complete native datatype theory and public API:
- `Sort::Datatype(DatatypeSort)` with `DatatypeConstructor` / `DatatypeField`
  (`../ay ay-core/src/sort.rs:56-132`).
- `Solver::try_declare_datatype(&DatatypeSort)` (`../ay ay-dpll/src/api/terms/datatypes.rs:78`).
- `datatype_constructor` / `datatype_selector` / `datatype_tester` term builders
  (+ `try_*` fallible variants) (`datatypes.rs:156/215/271/295/396/461`).

`try_declare_datatype` populates `is_constructor` / `datatype_iter`, which is exactly the
precondition for the mbqi tester-completion recognizers to fire — so the skipped-quantifier
soundness gate is satisfied by native completion instead of degrading to Unknown. The
exhaustiveness/tester/selector/injectivity facts become **native theory invariants** rather than
hand-asserted unbounded foralls, so model construction over symbolic datatype values succeeds.
Verified firsthand: a native-`Sort::Datatype` encoding of the exact witness returns
SAT/model_validated where the UF-over-Int encoding returns Unknown.

This uses ay's **existing** capability — **no ay edit**, so **no conflict with the concurrent
ay refactor** (which is solver-structure work: `ay-cp`→`aysolve-pb`, FlatZinc→`aysolve-fzn`).

## Touchpoints (bounded)

| File | Change |
|------|--------|
| `encoder/datatype.rs` (`register_datatype`) | Build a `DatatypeSort` from `TrustVcType::Datatype` and call `try_declare_datatype`; drop `carrier_sort = Sort::Int`; constructors/selectors/testers become native term builders, not UF `FuncDecl`s. |
| `encoder/datatype_axioms.rs` | **DELETE** — native theory replaces every hand-asserted axiom. |
| `encoder/types.rs` (`sort_for_type`) | Map `TrustVcType::Datatype{..}` → `Sort::Datatype(..)` (currently → `Sort::Int`). The single highest-risk change: every consumer that assumed a datatype term is `Sort::Int` must accept `Sort::Datatype`. |
| `ir.rs` / `prepared_context.rs` / `prepared_context/type_env.rs` | `to_datatype_type` / type→sort resolution consistency; `resolve_trait_impl_concrete_types` already yields a Datatype — now it carries a real native sort. |
| `vc_extraction.rs`, `encoder/verification/setup.rs` | Registration call-site wiring (already calls `register_builtin_datatypes`). |
| `ir_lowering/dispatch/methods.rs` + field-access lowering | Constructor/selector/tester `FnCall` resolution must route to native builders (the `variables`/`fn_ctx.functions` insert at datatype.rs:120-130 is replaced by native term construction). |

## Incremental, gated execution plan

The blast radius is large (16085 lib tests assume UF-over-Int). Execute in small, individually-
gated increments — **never** flip the manifest mid-migration, **never** weaken a test to absorb a
flip; triage every flip as improvement (Unknown→decided) vs regression (decided-sound→Unknown).

- **P0 — pure builder, no behavior change.** Add `fn datatype_sort_for(ty: &TrustVcType) ->
  DatatypeSort` (variants → `DatatypeConstructor`, fields → `DatatypeField` with recursively-
  resolved field sorts). Unit-test it in isolation. No registration path changed yet. Lib must be
  byte-identical green.
- **P1 — native registration + sort, behind the existing datatype path.** Switch
  `register_datatype` to `try_declare_datatype` + native term builders; `sort_for_type` →
  `Sort::Datatype`; delete `datatype_axioms.rs`. Rewrite `encoder/tests/datatype/
  registration_axioms.rs` to assert **native registration** (it currently asserts the hand-rolled
  axioms exist — that's a legitimate test-intent change, NOT a weakening, but must be called out
  explicitly and reviewed). GATE: `targo build --workspace` + full lib green with every flip
  triaged; the symbolic-self witness (`let v=c.get(); assert(v==5)`) VERIFIES; the non-conforming
  (`{6}`) variant still NOT-Verified; manifest untouched.
- **P2 — recursive datatypes.** Confirm `recursive_well_foundedness` / `recursive_size_usage` /
  `match_datatype` behave under native sorts (size/decreases reasoning may need the native selector
  form). Adjust + re-gate.
- **P3 — opportunistic promotions.** Only after P1-P2 are green, re-run the collection files
  (`seqs`/`sets`/`vec`/…) under the corpus refresh to see which now verify end-to-end; promote ONLY
  whole files that pass `evidence --run-trust-vc-corpus --refresh-trust-vc-corpus-evidence` with
  non-empty source hashes, per the standing integrity rules. Expect partial — each file still has
  its own non-datatype tail.

## Soundness

Native datatype theory is ay's own sound theory; replacing hand-asserted axioms with it cannot
introduce unsoundness (it is strictly more principled). The witness verifying is a **completeness**
gain, not a soundness change. The mandatory adversarial guard at every gated step is unchanged: a
non-conforming impl / false claim must still fail closed. If any previously-Verified **sound**
program turns Unknown/Counterexample under native sorts, that is a regression to fix or the
increment blocks — it is never absorbed by editing the test.

## Risk / honesty notes

- This is multi-tick. The verus-replacement **count does not move** until P3 lands a whole file —
  do not imply otherwise.
- `sort_for_type → Sort::Datatype` is the change most likely to cascade (sort mismatches at every
  datatype consumer). If P1 proves the cascade unbounded, fall back to keeping `Sort::Int` as the
  carrier but **also** calling `try_declare_datatype` so the recognizers fire — investigate whether
  native completion works with an Int carrier (it may not; `mbqi.rs:1015` keys on the constructor's
  datatype, which needs the native sort). Record the finding either way.
