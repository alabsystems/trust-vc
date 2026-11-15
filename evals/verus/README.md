# Upstream Verus Corpus Evidence

This directory tracks evidence for upstream Verus tests used in TrustVc parity
work. The manifest is intentionally conservative: an upstream Verus test is not
considered accepted until it has an explicit classification and the required
owner issue and reason fields.

## Files

- `upstream-verus-corpus.schema.json`: JSON Schema for corpus manifests.
- `upstream-verus-corpus.seed.yaml`: Seed manifest and policy for evidence-gate
  automation.
- `verus-tests.json`: Generated canonical manifest with one entry for each
  upstream `.rs` file under `source/rust_verify_test/tests` and
  `source/cargo-verus/tests`. This file is created by the evidence CLI once a
  pinned Verus checkout is available.
- `upstream-suite/`: what upstream Verus's own test suite does with its own z3 at
  the same pin, the reference for running a solver behind `VERUS_Z3_PATH`
  (`scripts/verus_suite/`). A solver baseline, not trust-vc engine coverage.

## Generating `verus-tests.json`

From the repository root, run:

```sh
./target/debug/cargo-trust-vc evidence --verus-path /path/to/verus --verus-rev <commit> --update-verus-tests-manifest --port-manifest-only
```

`--verus-path` may point at the Verus repository root or its `source/`
subdirectory. For manifest updates, strict evidence runs, and `--run-verus`, the
CLI also reads `TRUST_VC_VERUS_PATH` and then `VERUS_PATH` when `--verus-path` is
omitted. `--verus-rev` should be a concrete commit; for ordinary evidence runs
it may be omitted when `evals/verus/verus-tests.json` already has a pinned
`upstream.ref`.

The generator enumerates `.rs` files under `source/rust_verify_test/tests` and
`source/cargo-verus/tests` at the pinned git ref in the supplied checkout and
writes `evals/verus/verus-tests.json`. Existing entries with the same
`upstream_path` keep their classification, owner issue, reason, `trust_vc_paths`,
`evidence_kind`, `trust_vc_source_hashes`, and `expected_cases`; newly discovered
upstream tests are added as `classification: unclassified`.

The update fails if the existing manifest has duplicate `upstream_path` entries,
because preserving a classification would be ambiguous. Repair duplicates
manually, then rerun the command.

## Triage Summary

To inspect manifest progress without running replacement proof gates, run:

```sh
./target/debug/cargo-trust-vc evidence --corpus-triage-report --markdown
```

The triage report reads only the manifest and emits deterministic counts by
classification and top-level upstream path bucket, plus accepted executable
entries that still lack `trust_vc_paths` or reference missing TrustVc files. This is
not replacement evidence and does not relax the fail-closed gate policy below.
Current manifest state is not proven. **Recount rather than quote this
paragraph** — it is a snapshot, and it has rotted before:

```sh
jq '[.entries[].classification]|group_by(.)|map({(.[0]):length})|add' verus-tests.json
```

As recounted on 2026-08-28: 46 executable TrustVc port entries, 106
unsupported gaps, 4 not-applicable entries, 0 unclassified entries, and 6
machine-readable `known_gaps` notes spread over 3 ported entries. Those accepted
entries bind 51 repo-local TrustVc paths and 259 expected cases. Every
`unsupported-gap` entry has at least partial TrustVc path coverage (106 of 106);
across those rows the manifest records 1,990 expected cases and 332 explicit
`known_gaps` notes. Those cases document progress only and are not accepted
replacement evidence. Accepted entries use schema 2 source hash and
proof-obligation fingerprint pins unless they explicitly declare
`evidence_kind: cargo_trust_vc_integration_test`; cargo-wrapper integration-test
witnesses are wrapper evidence, not proof-obligation evidence, and TrustVc-only
Option closure-contract stress probes are regression-only.
The final replacement verdict remains blocked by the remaining unsupported gaps
and strict workspace/upstream Verus gates. The current canonical manifest must
cover both upstream-owned roots: `source/rust_verify_test/tests` and
`source/cargo-verus/tests`.

The replacement evidence report also emits `corpus.replacement_summary` in JSON
and a matching Markdown section. That summary keeps the headline proof counters
next to the gate result: accepted executable entries, accepted TrustVc path
bindings, accepted expected cases, unsupported gaps, unclassified gaps,
not-applicable entries, and accepted entries that still declare `known_gaps`.
The same report now includes structured `accepted_executable_ports` and partial
`unsupported_gap_evidence` arrays, plus matching Markdown tables. Use these to
audit the exact upstream path, owner issue, TrustVc path bindings, expected cases,
and proof-gap status without treating partial unsupported coverage as accepted
replacement evidence. The raw failure lists remain the source of exact blockers.

## Running Upstream Verus

For a replacement-proof attempt, include the upstream Verus runner:

```sh
TRUST_VC_VERUS_PATH=/path/to/verus ./target/debug/cargo-trust-vc evidence . --strict --run-trust_vc --run-trust-vc-corpus --run-verus --json --markdown
```

The default runner executes the upstream `rust_verify_test` package and
`cargo-verus` integration tests from the pinned checkout. A 100% replacement
verdict remains
fail-closed unless the Verus checkout exists, is a git worktree, is clean before
and after the run, and its `HEAD` matches either `--verus-rev` or the manifest
`upstream.ref`. Passing `--verus-command` is useful for local diagnosis, but that
override is not accepted as replacement evidence.

## Scaffolding Port Stubs

To create fail-closed placeholders for entries that still need TrustVc ports, run:

```sh
./target/debug/cargo-trust-vc evidence --scaffold-verus-port-stubs --markdown
```

Use `--port-output-dir <repo-local-dir>` to choose a different repo-contained
output directory; the default is `evals/verus/ported`.

The scaffold command reads the manifest and skips replacement gates. It targets
only `unsupported-gap` and `unclassified` entries, mirrors upstream paths
relative to either declared upstream test root, creates missing parent
directories, does not overwrite existing files, and reports created, existing,
and skipped entries. Generated files intentionally contain no TrustVc-annotated
functions, so they remain fail-closed until replaced by real ports and the
manifest entry is changed to `ported` with the generated path in `trust_vc_paths`.

## Gate Policy

Evidence gates should load the manifest, enumerate the upstream Verus test corpus
for the pinned `upstream.ref`, and fail when any condition is true:

- An upstream test path has no manifest entry.
- A manifest entry is stale and no longer appears in upstream enumeration.
- The manifest has duplicate `upstream_path` entries.
- `gate.failing_classifications` does not include both `unclassified` and
  `unsupported-gap`.
- `upstream.repo` is not `https://github.com/verus-lang/verus`.
- `upstream.test_roots` is not exactly
  `["source/rust_verify_test/tests", "source/cargo-verus/tests"]`.
- A manifest entry has `classification: unclassified`.
- A manifest entry has `classification: unsupported-gap`.
- The Verus checkout is missing, not a git checkout, dirty before or after
  evidence commands, or its `HEAD` does not match the concrete pinned revision.
- A `ported` or `unchanged` entry lacks `trust_vc_paths`, references a missing
  path, or escapes the repo.
- A `ported` or `unchanged` entry names a directory that is not a cargo fixture
  with `Cargo.toml`.
- A `ported` or `unchanged` entry lacks `expected_cases`, has duplicate or
  invalid case IDs, observes missing or unexpected TrustVc cases, observes the
  wrong verdict, or captures fewer obligations than declared.
- A `ported` or `unchanged` entry declares an invalid `evidence_kind`. Missing
  `evidence_kind` defaults to `proof_obligation`.
- A multi-path `ported` or `unchanged` entry has an `expected_cases` item
  without `trust_vc_path`, or observes a case outside the declared path for that
  expected case.
- A multi-case or split-path port's `expected_cases` omit `upstream_case_id`
  values needed to map observed TrustVc cases back to the pinned upstream Verus
  harness cases.
- A `ported` or `unchanged` entry declares any `known_gaps`.
- A `ported` or `unchanged` `proof_obligation` entry uses a
  `crates/cargo-trust-vc/tests/*.rs` integration-test path, uses
  `min_obligations: 0` for a non-error expected verdict, omits required
  `obligation_fingerprints`, pins duplicate fingerprints, relies on duplicate
  observed condition hashes to satisfy `min_obligations`, or has a non-error
  observed case without fingerprints.
- A `ported` or `unchanged` `cargo_trust_vc_integration_test` entry has a
  `trust_vc_paths` value outside `crates/cargo-trust-vc/tests/*.rs`, lacks
  `expected_cases`, declares an expected verdict other than `verified`, uses
  nonzero `min_obligations`, or declares `obligation_fingerprints`.
- A `proof_obligation` corpus result uses an execution mode other than
  `direct_source` or `cargo_fixture`, or a `cargo_trust_vc_integration_test`
  corpus result uses an execution mode other than
  `cargo_trust_vc_integration_test`.
- Corpus execution uses a `cargo-trust-vc` executable outside this repo's
  `target/` directory or cannot record its executable hash.
- A `not-applicable` entry is neither
  `source/rust_verify_test/tests/common/mod.rs`, an upstream file whose
  extracted harness cases are all `#[ignore]`, nor one of the #2780
  cargo-verus harness helpers
  `source/cargo-verus/tests/src/fake_cargo.rs` or
  `source/cargo-verus/tests/src/utils.rs`.

The `unclassified` value exists only as a bootstrap state. It is not an accepted
classification. `unsupported-gap` is useful while triaging gaps, but it is not
accepted evidence for a 100% Verus replacement claim.

Generated entries are intentionally fail-closed: every new upstream test starts
as `unclassified`, so replacement proof remains blocked until that entry is
triaged into an accepted classification with a real owner issue and reason.

## Entry Classifications

Use one of the review classifications once a test has been reviewed:

- `unchanged`: The upstream Verus test is expected to run without source changes.
  Include at least one repo-contained `trust_vc_paths` entry and the exact
  `expected_cases` set.
- `ported`: The upstream test has a TrustVc-specific port. Include the ported
  path in `trust_vc_paths`, declare the exact `expected_cases` set, and use
  `reason` to describe the material differences.
- `unsupported-gap`: The test covers a known unsupported gap. Use `owner_issue`
  for the tracking issue that owns the gap. This is reviewed triage, but it is
  still a failing classification until the gap is closed.
- `not-applicable`: Accepted for
  `source/rust_verify_test/tests/common/mod.rs`, the shared upstream helper
  module, upstream files whose extracted harness cases are all `#[ignore]`, and
  the #2780 cargo-verus harness helpers
  `source/cargo-verus/tests/src/fake_cargo.rs` and
  `source/cargo-verus/tests/src/utils.rs`. Any broader exclusion requires a
  code allowlist change.

Every entry must include:

- `upstream_path`: Path within the upstream Verus repository.
- `classification`: One of `unchanged`, `ported`, `unsupported-gap`,
  `not-applicable`, or bootstrap-only `unclassified`.
- `owner_issue`: Issue URL or repo-local issue reference for the person or lane
  responsible for the classification. Accepted classifications must use a real
  issue reference; `TBD` is reserved for failing `unclassified` seed entries.
- `reason`: Short, reviewable explanation for the classification.

Prefer one upstream test file per entry. If an upstream test expands into several
TrustVc tests, keep one entry and list all corresponding `trust_vc_paths`. When an
entry has more than one `trust_vc_paths` value, every `expected_cases` item must
declare the exact `trust_vc_path` that may satisfy it. Each case ID is the TrustVc
function name observed by the evidence runner, and the observed source must be
the declared file or be under the declared cargo fixture directory. If a port
has multiple expected cases or splits one upstream Verus harness case into
multiple TrustVc cases, set `upstream_case_id` on each case. Single-case entries
may still omit it and default to `case_id`. The expected verdict is `verified`,
`counterexample`, or `error`.
Accepted entries may declare `evidence_kind`. Omitted values default to
`proof_obligation`, which is the strict proof-closure mode: `min_obligations` is
the minimum number of non-assumed captured obligations that must be present for
that case, non-error verdicts must declare at least one obligation, and pinned
`obligation_fingerprints` must be unique. Duplicate observed condition hashes
count once toward `min_obligations`. Expected-error proof-obligation cases may
declare zero obligations only when the parse, extraction, or verification error
is the upstream behavior being mirrored.
Use `evidence_kind: cargo_trust_vc_integration_test` only for wrapper witnesses
under `crates/cargo-trust-vc/tests/*.rs`; each expected case must be `verified`
with `min_obligations: 0` and no `obligation_fingerprints`.
If an accepted entry must exercise a TrustVc CLI gate, `trust_vc_check_args` may
currently declare only `--no-cheating`; negative gate cases are still modeled as
explicit `expected_verdict: error` cases with `expected_error_patterns`.

### TWO LAYERS: every accepted case's DECLARATION, 51 cases' PROGRAM

**LAYER 1 — per-case upstream checks, scope 259 of 259 — and its sub-checks do
NOT share that denominator.** The upstream harness-case block in
`load_corpus_report_with_options` runs for EVERY accepted entry and parses the
upstream file with `syn` (`upstream_verus_harness_cases`). Two of its checks are
corpus-wide, on all **259 of 259**: the upstream case EXISTS and is not
`#[ignore]`d, and the DECLARED VERDICT EQUALS upstream's extracted verdict. The
rest are narrower, each on the population named with it: the number of mapped
port cases is compared **per upstream case, over the 223 the corpus maps** —
exactly on the **50** that state a failure count, `>=` on the other **173**;
every diagnostic message upstream ASSERTS is declared verbatim (**16 strings
over 16 of the 25** `error` cases, and nothing on the other 9); every verifier
WARNING upstream content-checks is declared (**1 upstream case**); every
FORBIDDEN diagnostic-context pattern upstream states is declared (**1 upstream
case, 1 pattern**); and an upstream RUST-error case maps to a cargo fixture
(**4 of the 259**). In the run lane the 16 upstream-asserted strings compose
with `append_expected_error_pattern_failures`, which requires every declared
pattern to appear in ONE failure-attached diagnostic the PORT emitted — so
upstream's exact message has to come out of trust-vc's own run.

Round 9's review finding, recorded rather than quietly fixed: the sentence this
paragraph replaces, and the bound's own headline, credited the verdict
comparison, the occurrence count and the upstream-asserted messages all to 259.
That is right for the first and wrong for the other two. The forbidden-pattern
check was missing from the list entirely, which understated Layer 1 in the
other direction.

What Layer 1 does NOT establish: anything about whether the port's PROGRAM
reproduces upstream's. **A faithful declaration over an unfaithful body passes
this layer.** It is nonetheless live and still RED — this worktree's
`--verus-path ../verus` run returns 1 `upstream_case_failure`: a missing
upstream diagnostic pattern on the ERROR case `real.rs::test_reject_mixed`.
`upstream_case_failures.is_empty()` is a conjunct of the corpus manifest gate's
pass condition, so it blocks. The six that used to sit beside it were all on
`z3_restart.rs`'s `multiset_basics` (five verdict mismatches on VERIFIED cases,
one occurrence-count mismatch) and they went by fixing the RULE, not the
manifest: upstream's case is a SIX-FUNCTION program with ONE failure, so the
exact count belongs on the mapped cases that DECLARE a failure, and the other
five mapped cases are the functions upstream does not fail. No declared verdict
moved.

**LAYER 2 — source-level correspondence, scope 51, established 51.** Everything
in the rest of this section applies to `counterexample` cases and to nothing
else. `append_counterexample_identity_failures` returns immediately when the
expected verdict is not `counterexample`, so a `verified` case reaches no claim
comparison, no premise channel and no vacuity guard. Measured on this manifest:
of 259 accepted expected cases, **51 are PROGRAM-correspondence SCOPED
(`counterexample`) — 19.7%, one case in five — while 183 (70.7%) are pinned by
an obligation COUNT and an engine-derived fingerprint of the PORT'S OWN
obligations alone (`verified`), and 25 (9.7%) by diagnostic patterns
(`error`)**.

**SCOPE IS NOT RESULT, and every bucket now states both.** A rule's scope is how
many cases it COVERS; what it ESTABLISHES is that minus whatever it refuses,
cannot read, or synthesizes. The headline, recounted by the gate against the
pinned checkout: **of the 259, 51 (19.7%) have their PROGRAM compared with
upstream's, and 51 (19.7%) survive that comparison to establish anything** — the
gap between scope and established is EMPTY, and it was two kinds. 0 are now
REFUSED as un-checkable: the CLAUSE-MARKED class (upstream marks the function
HEADER) was refused for as long as a header mark drew an EMPTY premise window,
and its window is now the function BODY, because a contract obligation is
discharged against everything the body runs. 0 more can only FAIL their
cross-check: that class held `harness.rs::harness_false` until the LINE-BASED
region reader learned upstream's plain `#[test]` + `fn name()` form, and it is
empty too. The other 208 (80.3%) have their DECLARATION checked and their
PROGRAM not. Inside the 51, 19 are checked against an EMPTY upstream premise
window (15 of those reach no definition either), so they are constrained by the
claim and the hypothesis list and little else.

The `error` bucket, first measured in review round 7 and re-framed in round 8:
Layer 2 covers 0 of it, Layer 1 covers all 25, and it establishes 25 port-side
diagnostic pins — 25 of the 25 declare at least one `expected_error_patterns`
entry, so the pin is non-vacuous on every one — plus, on 16 of the 25, an
upstream-asserted message that must be declared verbatim AND appear in the
port's own failure diagnostic. The other
9 have no upstream-asserted message at all: upstream marks `// FAILS` and calls
`assert_one_fails`, and the extractor re-keys such a case to `error` when
upstream runs it with `--no-cheating`, so those 9 are upstream REFUTATION cases
the port runs on trust-vc's own `--no-cheating` CLI surface. Seen from the
port's side, with a generous substring scan of the literals upstream asserts:
of the 48 declared `expected_error_patterns` only 18 appear inside a string
literal upstream itself asserts; 14 of the 25 cases have every pattern so
sourced; 10 — every `no_cheating.rs` case — declare the port's own fixture path
and wording; and 1 (`harness.rs::harness_invalid_rust`) names an upstream case
the LINE-BASED region reader cannot see, though Layer 1 reads it. The 30
declared patterns that are not upstream text are a manifest-authoring question
no rule asks.

The 183 split AGAIN, and the second split matters because the first sentence is
false for part of it. **135 of the 183 are AUTHOR-pinned** — a
`min_obligations` greater than 0 that an author chose, and fingerprints of
obligations the engine really built. **The other 48 are SCHEMA-FIXED**: every
expected case of the six `cargo_trust_vc_integration_test` entries (upstream's
`source/cargo-verus/tests/*`). For those entries the schema REQUIRES
`expected_verdict: verified`, REQUIRES `min_obligations: 0` and REFUSES any
`obligation_fingerprints`, and the runner never invokes the engine — it
synthesizes `verified` with obligation count 0 whenever
`cargo test --test <target> -- --exact <case_id>` reports exactly one pass. So
the count pins nothing there, because the schema wrote it; `verified` on those
rows is a schema placeholder, not an engine verdict. What they establish is a
real but different thing: a named, non-`#[ignore]` `#[test]` under
`crates/cargo-trust-vc/tests/` passes — a CLI-behaviour witness for the
`cargo verus` argument-forwarding compat layer. The deleted-body sentence below
applies to these 48 with LESS resistance: emptying the test body makes it pass
and no OBLIGATION pin moves, because there is none. The only manifest field that
changes is the `trust_vc_source_hashes` sha256 of the port file — which all 46
accepted entries carry alike, and which the refresh re-stamps to whatever the
file now says, so it separates these 48 from nothing. The proof-content ratchet
compares `min_obligations` and `obligation_fingerprints` and nothing else, so it
has nothing to see on any of the 48, ever.

Recount rather than quoting those figures — every rendering of the
replacement summary prints the split AND the percentage under the accepted-case
total, `scripts/corpus_coverage.py` prints the same block under its own
accepted numbers, and `accepted_case_correspondence_bound` in the machine
output states the bound.

The bound also lives in the manifest itself. Schema v2 carries a top-level
`correspondence_bound` string, and the gate REFUSES to load a v2 manifest whose
copy is absent, empty or one byte different from the constant in `evidence.rs`.
Re-wording the bound therefore means editing the constant and copying the new
text across in the same commit; a successful refresh re-stamps the field to keep
it current, but it cannot repair a manifest the gate has already refused to
load. The accepted-case count and
the statement of what it does not establish are one artifact: to weaken the
claim you change the constant in the gate, under review, not a string in a data
file.

**The bound's last section is `(6) OUTSTANDING REVIEW FINDINGS`**, and it is
there so that a finding against the bound's own prose never has to choose
between blocking a branch and being lost. A finding recorded there is
DISCLOSED, not fixed: the prose above it still says what it said. Appending one
is a single edit to `ACCEPTED_CASE_CORRESPONDENCE_BOUND` (a `[R<round>] ` entry
after `FINDINGS:`, deleting the `NONE OUTSTANDING.` sentinel) plus a re-stamp,
because the section is part of the same string and travels into the manifest
under the same byte-identical check as every other sentence. Both markdown
renderings print the list, empty or not.

What that means for the weak bucket, stated plainly because five adversarial
rounds each found the strongest unqualified reading: **a `verified` port whose
function body is deleted, with `min_obligations` lowered to match and the port
committed, is ACCEPTED.** It was measured in review round 5 on
`scope.rs::test1`. Nothing in this section refuses it, and the fix is not
another source-level rule — see "The route that closes this" below.

A `counterexample` case DECLARES NOTHING about the upstream line it reproduces.
There is no `upstream_marked_line` field and there never will be one: a
port-authored selection anchors nothing. Every text the correspondence rule
compares is machine-derived — the port's from the engine's own located
refutation, upstream's read straight out of the pinned Verus checkout.

What the gate requires of a `counterexample` case is: exactly ONE refuted
obligation (upstream `assert_one_fails`) and no UNDECIDED one; the port's own
`// FAILS` marker somewhere on the statement the engine ACTUALLY REFUTED; and
that statement, canonicalized, EQUAL to upstream's own `FAILS`-marked line or to
the statement that line sits in, canonicalized the same way. Canonicalization is
not byte-parity — it maps the deliberate native-surface differences onto the
claim they spell (`!(P) || Q` for `P ==> Q`, `assert_by_bit_vector!(..)` for
`assert(..) by(bit_vector)`, an `#[ensures(..)]` attribute for a clause line,
`1usize` for `1`) and nothing else. Two cases mapped to one upstream case may
not claim a line more often than upstream marks it.

The port's marked LINE is a LOCATOR only and is never itself compared: it may
sit on any line of the refuted statement, which is what upstream searches, so
comparing it would let a port bury upstream's claim inside a bigger, trivially
false statement.

The claim is not the whole comparison. A statement's claim is not determined by
its own text — `assert(5 <= i)` is upstream's unprovable claim under
`let i = choose|i: int| f(i);` and a ground falsehood under `let i = 0;` — so
the refuted claim is compared UNDER ITS PREMISES, and every premise text is
machine-derived on both sides exactly as the claim is. Four channels, each a
place a port could otherwise rewrite meaning while leaving the marked line
byte-identical:

* the `let` BINDINGS in scope at the refutation, compared by initializer
  (canonicalized, type ascription dropped) for every identifier the claim
  reaches, transitively;
* the HYPOTHESES the enclosing function states — `#[trust_vc::requires(P)]`
  attributes here, a `requires` clause list upstream — compared as the SET OF
  CONJUNCTS, so merging two clauses into one `&&` corresponds and dropping one
  does not;
* the DEFINITIONS the claim calls, compared by canonicalized BODY, so
  `#[trust_vc::spec] fn f1(..) { i + 1 }` and upstream's `spec fn f1(..)
  { i + 1 }` are one definition and a rewritten body is not;
* the STATEMENTS the function runs before the refuted one, compared as
  EQUALITY, so an added `assume!` or an inserted `if` guard has to appear on
  upstream's side too AND a statement upstream runs may not be deleted.

The clause KIND is compared separately from the text, because upstream writes
`ensures` on one line and marks the bare clause on the next: the port's kind is
read from the ENGINE's own obligation kind, not from the attribute, and it is
compared only when upstream's marked line sits in a clause list.

### An identifier-free claim is held to the WHOLE environment

The binding, definition and reachability channels are keyed on the identifiers
the CLAIM reaches. `assert(false)` reaches none — and `assert(false); // FAILS`
is upstream's own marked line across much of this corpus — so for such a claim
those channels compare nothing at all. A check that cannot discriminate must
REFUSE, not accept, so when nothing was compared (no hypothesis on either side
and not one identifier of the claim bound or defined by either side) the case
must correspond on the whole premise environment instead: upstream's statement
set exactly, and upstream's BINDING set in full rather than by reachability.

### Proof content ratchets UP — against `HEAD`, and only against `HEAD`

`min_obligations` and the pinned `obligation_fingerprints` are what a case
commits to having PROVEN. Neither the count nor the size of the pinned set may
fall below the COMMITTED manifest's, and `--refresh-trust-vc-corpus-evidence`
refuses to write a run that would lower either. An intentional decrease is
declared on the case:

```yaml
      obligation_decrease_waiver:
        from_min_obligations: 6
        reason: re-keyed to upstream's split case
```

`from_min_obligations` must name the committed count being descended from, so
one waiver authorizes one decrease and not the next; every accepted decrease is
reported in the corpus report's `proof_content_decrease_waivers`. Fingerprint
IDENTITY is deliberately NOT ratcheted — a fingerprint is an engine-derived
hash of the encoded obligation, so an encoder change rehashes the whole corpus
without any port losing a thing.

**CORRECTION — this is a trip-wire on a DIFF, not a refusal by construction,
and an earlier revision of this section read as an absolute.** The check
compares the WORKING manifest against `git show HEAD:<manifest>`. It therefore
refuses a decrease exactly while the decrease is uncommitted (a hand-edit, or a
refresh that would write one). **Commit the lowered pin and the working
manifest equals `HEAD`, there is nothing left to compare against, and the check
is silent about that case forever after** — measured in review round 5. What it
buys is real and smaller than it sounded: a committed decrease must be a line
in a reviewed diff. A high-water field stored in the entry would move the
launder one step (the port author controls that field too), not close it.

### What correspondence does NOT compare — read the number with these in view

The rule decides on SOURCE TEXT, which is not the obligation the solver saw.
These are open, named, and not closed by the rules above:

* **Every `verified` case — the largest hole by far, and the majority of the
  accepted-case total.** Correspondence is never reached for them; they are
  pinned by an obligation count and a fingerprint set and by nothing that looks
  at upstream's source at all. A gutted body with a matching lowered count is
  accepted. See "SCOPE FIRST" above.
* **Every `error` case.** Pinned by diagnostic patterns.
* **The signature and the type environment.** A port may keep upstream's
  statements, bindings and hypotheses byte-identical and declare
  `fn f(x: u8)` where upstream declares `fn f(x: int)`. `x * z < y * z` over
  `u8` is a far cheaper refutation than over `int`, and nothing here sees the
  difference. `strip_numeric_literal_suffixes` erases width from the claim
  itself for the same reason it erases it from a literal.
* **Anything outside the enclosing function and the definitions the claim
  calls** — datatype declarations, trait impls, `broadcast` lemmas in scope.
* **Statement ORDER and multiplicity.** The statement channel is a SET.
* **BLOCK STRUCTURE.** The binding channel compares name/initializer PAIRS as a
  SET, so an inner `{ let mut x = 5; x = 50; }` and the same two lines flattened
  into the enclosing sequence present the same pair set and the same statement
  set. Measured on `scope.rs::test1_fails` — which IS upstream's block-scope
  case, in the one file whose entire subject is scope: delete the inner block,
  flatten and reorder every binding, and both channels are unmoved, the case
  passes, and the refresh re-stamps the hash. Pinned as a disclosure by
  `block_structure_and_statement_order_reach_no_premise_channel`; if that test
  ever fails, the hole is closed and this bullet must go in the same commit.
* **A `let` this reader cannot bracket** (a block longer than its 24-line
  window) reaches neither channel, on either surface.

### One class was refused, and is now CHECKED: CLAUSE-MARKED obligations

When the refuted obligation is a contract CLAUSE on both surfaces — upstream's
`ensures P // FAILS` in a signature clause list, the port's
`#[trust_vc::ensures(P)]` attribute — the marked line is a function HEADER line.
`enclosing_function_prefix_lines` used to return EMPTY for a header line (no
`let` is in scope on a signature), so both premise windows were empty BY
CONSTRUCTION, whatever either function did, and the FUNCTION BODY — which is what
makes a clause refutable at all — reached no channel.

Measured on `z3_restart.rs::test2_fails` (upstream: `requires x > y, 3 <= z;
ensures y * z > x // FAILS` over an EMPTY body): a port body stuffed with ground
`assume!`s collapses the nonlinear postcondition to an arithmetic falsehood and
presented byte-identical binding, statement and hypothesis channels — zero
failures of any kind. The hypothesis channel does compare the `requires` list,
which is why the round-4 vacuity guard never fires for it; the launder is in the
body, not the clause list. The class was therefore **REFUSED as un-checkable**,
which established nothing about three of the corpus's counterexample cases.

**It is fixed at the WINDOW, not at the refusal.** A contract obligation is
discharged against everything the function body runs — an `ensures` holds at
every return — so a header mark's premise window is that BODY, drawn by the same
reader on both surfaces. The grounded port's three `assume!`s now land in its
statement set against upstream's empty one, and the statement channel compares
as EQUALITY, so the launder FAILS a real comparison instead of being refused.
`a_clause_marked_obligation_is_checked_against_the_function_body` pins both
halves: faithful corresponds, grounded fails on the statement channel.

What is still refused, fail-closed and with **0 members in this corpus**, is the
shape where UPSTREAM ITSELF has no body to read — a header mark on a bodyless
signature, where the text that makes a clause refutable is missing on upstream's
own side. `UpstreamFailsMark::window_undrawable` is that fact, computed by the
same reader that draws the window, out of the pinned checkout.

Two earlier keys for the refusal were wrong and both stay recorded, because the
second is why `nonlinear.rs::test_requires` was never in this class:

* the PORT obligation's `kind` string was INERT. Measured end to end, the engine
  reports a refuted postcondition as `kind: "assert", name: "postcondition"` and
  a by-assert `requires` as `kind: "verification_step"`, never as `"ensures"` or
  `"requires"`, so a port-side clause-kind test sees nothing. (The same
  measurement makes the clause-KIND comparison in `premise_correspondence` inert
  on this corpus; it is kept and disclosed at its own test.)
* upstream's `clause_kind` alone OVER-refused. A clause line is not always a
  header line: `nonlinear.rs::test_requires` marks the `requires` clause of a
  BODY-level `assert(..) by(nonlinear_arith)`, whose window is the statements
  before that assert — of which there are none, because it is the function's
  first. That emptiness is a fact about upstream's program which the port must
  reproduce, since the statement channel compares as equality;
  `a_body_level_clause_mark_is_not_refused_as_uncheckable` pins it.

Measured cost on the pinned manifest: **0 of the 51 `counterexample` cases**.
`nonlinear.rs::test1_fails`, `nonlinear.rs::test2_fails` and
`z3_restart.rs::test2_fails` — the three this class used to hold — are checked
against upstream's own body now.

### The route that closes this

The complete answer is not a further source-level rule. Five rounds of them
have each been laundered by the next reader, the fifth by stepping round the
rule entirely into the `verified` cases. It is to decide correspondence on the
ENCODED OBLIGATION — hypotheses plus goal, which the engine already builds for
the port and would build for upstream — which needs a **Verus-to-IR import**:
upstream's case compiled through `trust-ir` into an encoding, so the two
obligations are compared as formulas rather than as prose. That import also
closes the `verified` hole, because a verified case has no refuted claim to
compare but does have an obligation set. It is a project, not a patch.

Concretely, four parts:

1. **A Verus-to-IR import**, so upstream's case has an encoding to compare
   against at all. `verus!` source through the trust-vc frontend into `trust-ir`
   is the self-contained shape; `.vir` interop is the Phase-2 alternative.
2. **A per-CASE entry point** — already provided: the corpus extracts the
   upstream `#[test] <name> verus_code! { .. }` region today.
3. **Obligation-SET comparison in the calculus, not in strings**:
   alpha-equivalence plus the normalizer the canonicalizer already implements
   for the deliberate native-surface differences, set equality on the
   hypotheses, entailment-or-equality on the goal.
4. **A pinned Verus build, or a vendored corpus, at the manifest's upstream
   ref**, so the comparison is reproducible from the pin.

Until it exists, read the accepted-case count as exactly this and no more:

* an accepted `counterexample` case — "the port refutes upstream's marked
  claim, in a function that runs upstream's statements and binds what upstream
  binds", NOT "the port reproduces upstream's proof obligation";
* an accepted `verified` case — "the port verifies, and discharges at least
  the pinned number of obligations", with NO established relation to upstream's
  source;
* an accepted `error` case — "the port produces a diagnostic matching the
  declared patterns".

## Minimal Entry

```yaml
- upstream_path: source/rust_verify_test/tests/example.rs
  classification: ported
  owner_issue: https://github.com/alabsystems/trust-vc/issues/1234
  reason: Ported Verus header clauses to TrustVc proc macros.
  trust_vc_paths:
    - evals/verus/ported/example.rs
  trust_vc_source_hashes:
    - path: evals/verus/ported/example.rs
      kind: file
      sha256: sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
  expected_cases:
    - case_id: example_header_clause
      expected_verdict: verified
      min_obligations: 1
      obligation_fingerprints:
        - sha256:abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789
```
