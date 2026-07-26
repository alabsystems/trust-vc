# Design: incompleteness-Unknown as a verification failure (Verus-faithful)

**The sound resolution to the `real_nonlinear2`-class blocker** — the verdict-
taxonomy conflict that makes trust-vc *more precise* than Verus and thereby
*diverge* from it. From a read-only gate-mechanics investigation (2026-06-02).
This is a **general** unblock (a whole class of "Verus relies on Z3-unknown-as-
fail" cases), not a one-off, and it is sound (no fabricated model, no gate
relaxation).

## The gap (verified against the gate code)

- The gate compares observed-vs-expected verdict by **exact string equality**
  (evidence.rs:5950-5956). Expected side has 4 labels: verified / counterexample /
  error / verified-blocker — **no `unknown`** (evidence.rs:1100-1110).
- Upstream `assert_one_fails`/`assert_fails(N)` derives to **`counterexample`**
  (err_helper_verdict, evidence.rs:9046-9068). Crucially, `assert_one_fails`
  (verus common/mod.rs:735-744) only checks there is exactly ONE error span
  containing the `FAILS` marker — **it never inspects a model/counterexample.**
- **How Verus produces that failure:** an SMT `unknown` from genuine
  incompleteness becomes `ValidityResult::Invalid(None, None, None)` — a
  verification FAILURE with **no model** (air/smt_verify.rs:279-326, 415-418).
  (A resource/rlimit `unknown` becomes the *separate* `Canceled` outcome.)
- trust-vc maps ay's NRA `Unknown` → `VerdictKind::Unknown` → label `unknown`
  (verify.rs:523-525), which `!= counterexample` → blocking reason → NotProven.

So the divergence is purely: **Verus reports incompleteness-unknown as a
model-less failure (= the gate's "counterexample"/assert_fails); trust-vc reports
a distinct `unknown`.**

## The sound fix

1. **Split `Unknown` by cause.** `VerifyResult::Unknown { reason, category }`
   already carries the cause. Distinguish (a) genuine solver **INCOMPLETENESS**
   (NRA/nonlinear/incomplete-quantifier — the fact may be valid but is unprovable
   in the available theory) from (b) **RESOURCE** exhaustion / cancellation /
   timeout. Use `category`, never string-guessing. (Mirrors Verus
   smt_verify.rs:279-326.)
2. **Introduce a no-model verification-FAILURE outcome** (analogue of Verus
   `Invalid(None,None,None)`): an obligation not discharged, **no model, no
   fabricated counterexample narrative.** Report an *incompleteness*-`Unknown` on a
   proof obligation as this failure, and map it to the gate's `counterexample`
   expectation (since that label means "assert_fails", not "a model exists").
3. **Resource-`Unknown` stays `Unknown`** — a timeout does NOT mean the fact is
   false (more resources might prove it); reporting it as a failure would be
   wrong. This split is the load-bearing soundness boundary.

## Why it's sound (not gaming)
- Reporting "this assertion was not proved → the function does not verify" is the
  **conservative** interpretation — you never claim verification you didn't
  achieve. No model is fabricated.
- It **matches Verus exactly** (same model-less failure), so it is faithful
  replacement, not gate-relaxation.
- It only ever turns an *incompleteness* non-proof into a failure — which is
  always a sound verdict (a true-but-unprovable fact correctly does not verify; a
  false fact correctly fails).

## Blast radius — gate hard
This changes how `Unknown` surfaces across the whole engine. It MUST:
- regress **zero** of the 40 accepted corpus entries (full `--run-trust-vc-corpus`),
- keep `trust-vc-core --lib` green,
- only reclassify INCOMPLETENESS unknowns (resource/timeout untouched),
- and be validated case-by-case (some existing entries may currently rely on the
  `unknown` label; verify each still matches after the split).

## Payoff: the first promotion
Combined with the in-flight `real.rs` bounded fixes (`nat_to_real`/floor-cast
encoding + `exists` parse-form) and the already-landed assumption-forwarding +
the already-live NRA proof of `real_nonlinear1`, this makes **all 6 `real.rs`
cases** match their upstream verdicts → the first legitimate promotion
**40 → 41**. Real, verified, never gamed.
