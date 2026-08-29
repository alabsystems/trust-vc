# Design: Verus differential oracle + ay native theories (Hybrid accelerants)

> **SUPERSEDED IN PART (2026-08-28) — both levers have since been built, and §A's
> deliverable is no longer trust-vc's.** The differential oracle of §A lives in
> **ay**, as its `ay-z3-parity classify` subcommand; it was given that neutral
> home at R1 and extracted out of this repo (see
> `crates/cargo-trust-vc/src/lib.rs:50-53`), so the `--run-differential-oracle`
> wiring proposed in §A step 4 is not work to schedule here. On the §B side, ay's
> native Seq and String solvers shipped and are wired through
> `encoder/collection_seq_native/` behind the opt-in `native-seq` /
> `native-strings` features (`default = []`), so the remaining task there is
> adoption, not construction. The present-tense "building now" markers below are
> from 2026-06-02 and are retained as the original plan of record.

Concrete build plans for the two top levers of the internal grand-strategy-ay notes
(DECISION: Hybrid). From a pure-read design swarm (2026-06-02), grounded in the
actual Verus/ay/trust-vc code. **Soundness tripwire for both:** ay disagreeing with
Z3, or a native procedure deciding outside its sound fragment, is a *critical bug* —
flag/fail-closed, never silently accept.

## A. Verus differential oracle

Harvest per-query SMT2 from upstream Verus (with Z3's authoritative verdict), replay
each through ay's existing parse + `Executor::execute`, classify `(ay × z3)` into a
counted, reason-coded gap report. Drives **ay completeness** (bucketed by
`UnknownReason::code()`) *and* **trust-vc VC-gen self-check** (Verus-SMT2 vs
trust-vc-SMT2 for the same obligation, both run through the same ay).

**Mechanism (verified):** Verus logs replayable SMT2 via `--log smt` / `--log-all`
/ `--log smt-transcript` + `--log-dir DIR` (config.rs); the `.smt2` is a full
Z3-replayable script (prelude, asserts, `check-sat`, `get-model`). Thread flags
per-test via the harness's `VERUS_EXTRA_ARGS` env var; per-test attribution from the
`BucketId` filename prefix + span comment. **Polarity note:** Verus asserts the
*negation* of the VC — a *verified* goal is Z3 `unsat`, a *failing* goal is `sat`
(counterexample). The classifier must handle this exactly or it manufactures false
soundness alarms. The runner core already exists at
`crates/trust-vc-merge-runner/src/lib.rs:213-246` (`execute_smt`).

| Ph | Work |
|----|------|
| 0 | Per-test Verus SMT2 dumper (isolated; NOT global `VERUS_EXTRA_ARGS` over the whole suite — the log dir is clobbered per process; drive single tests, optionally `-V spinoff-all` for one query per function). |
| 1 | **First increment:** lift `execute_smt` into a standalone differential runner over **3 pinned seed `.smt2`** (one unsat/verified, one sat/counterexample, one ay-known-unknown): `ay_frontend::parse` → `Executor::execute` under a wall-deadline in `catch_unwind`; normalize unsat/sat/unknown; classify. No Verus needed. |
| 2 | Full-corpus sweep → counted JSON report in `reports/evidence/`, bucketed by `UnknownReason::code()` (ay gaps) and disagreements (soundness). |
| 3 | trust-vc VC-gen self-check mode: localize each failure as an *ay solver gap* vs a *trust-vc encoder gap* (same obligation, Verus SMT2 vs trust-vc SMT2 through the same ay). |
| 4 | Wire `--run-differential-oracle` into `gate.rs`/`evidence.rs`/`main.rs` alongside `--run-trust-vc-corpus`. |

**Risks:** ay≠Z3 verdict = SOUNDNESS bug (route to a hard-fail bucket); polarity inversion can mask/forge a disagreement; ground truth must be the *same* pinned z3 4.12.5; `Timeout` is incompleteness-excluded, not a gap.

## B. ay native theories (sidestep MBQI for collections)

Replace trust-vc's universally-quantified collection encodings (MBQI-fragile;
`MAX_MBQI_ROUNDS=5`) with **sound native QF decision procedures**, modeled on ay's
genuine array procedure (ROW1/ROW2 + extensionality, `ay-theories/arrays/src/lib.rs`).
Technique: convert each bulk collection axiom (a universal whose negation needs an
existential witness ay can only *guess*) into an **event-driven read-through /
congruence rule** keyed on ground subterms → decided by **saturation**.

| Ph | Work | Unblocks |
|----|------|----------|
| 0 | Baseline + fail-closed contract: histogram current `ay_incomplete` reason codes; pin the soundness contract (out-of-fragment ⇒ Unknown, never SAT/UNSAT). | — |
| 1 | **Native Set card+subset** (cheapest high-leverage; membership already QF over `Array(T→Bool)`): sound rules `card(empty)=0`, `card(insert)=card+ite(member,0,1)`, subset via saturation. **First increment.** | Set cluster |
| 2 | Native Multiset count-propagation (`Array(T→Int)`; insert/remove/count already QF). | Multiset |
| 3 | Native Map read-through (`Array(K→V)` + domain `Array(K→Bool)`). | Map |
| 4 | Native Seq higher-order (hardest; a TRUE ay gap — ay's seq solver returns Unknown for `seq.map`/fold). | Seq cluster |

**Unblocks:** the collection sub-cluster of the 112 (#2779 + collection-heavy #2777).
**Risks:** out-of-fragment SAT/UNSAT = critical soundness bug (worse than today's
Unknown); Nelson-Oppen combination must be sound when `card`/`count` bridge to LIA;
flipping the default encoding can change verdicts on already-green tests (gate on the
full lib suite + differential oracle).

## Build order

1. **Differential oracle Ph1** (the runner) — bounded, in-tree, the measurement tool. ← building now
2. **Oracle Ph0** (Verus SMT2 capture) — feeds it real data.
3. **Native Set Ph1** (ay) — first native procedure, in parallel.
4. Oracle Ph2-4 (corpus sweep + self-check + gate wiring) → drives everything else by counted data.
5. Native Multiset/Map/Seq; frontend-breadth swarms continue in parallel.
