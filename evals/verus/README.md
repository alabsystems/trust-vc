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
