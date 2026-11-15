# trust-vc-merge-contract

Versioned merge-boundary schema for trust_vc to trust_mc handoff.

## Version policy

- Current schema: `MergeBundle` v4 (`bundle_version = 4`) — the single source of
  truth is `MERGE_BUNDLE_VERSION` in `src/lib.rs`; read it there rather than
  trusting this line.
- Supported versions: 1 through `MERGE_BUNDLE_VERSION` (inclusive).
- v3 added an explicit `expression_format` field
  (`smt_lib2_term_v1`) declaring the grammar of `TypedExpr.expr` strings; v4 adds
  `FuncDeclMeta` / `FuelAxiomMeta` / `BroadcastLemmaMeta` (#2578).
- Unsupported versions are hard-fail:
  `MergeBundle::from_json_str` returns `MergeBundleError::UnsupportedBundleVersion`
  for versions outside the supported range.

This fail-closed behavior is intentional so trust_vc and trust_mc do not silently
accept incompatible bundle layouts.

## Expression format

v3 and later bundles use `expression_format: smt_lib2_term_v1`, meaning every
`TypedExpr.expr` string must be a canonical SMT-LIB2 **term** (not a full
script). Consumers assemble the surrounding `set-logic`, declarations,
`assert`, and `check-sat` scaffolding themselves.

## Corpus index

The authoritative fixture registry is
`fixtures/corpus_index.json`. Every parity fixture must be listed in
this file. The parity gate validates the index before engine execution
and fails closed on any inconsistency (missing manifests, extra on-disk
files, field drift, or status drift).

Downstream consumers should read `corpus_index.json` instead of scanning
the `fixtures/parity/` directory directly.

## Parity gate

The cross-repo M3 parity harness is executed from the trust_vc workspace:

```bash
python3 scripts/merge_parity_gate.py \
  --fixtures crates/trust-vc-merge-contract/fixtures/parity \
  --trust_mc-repo "$HOME/trust_mc" \
  --report "$REPORT_PATH" \
  --strict
```

The gate validates `fixtures/corpus_index.json` first, then runs
per-manifest prechecks, then executes engine comparison.

On success, the JSON report written to the configured `--report` path contains:

- `summary.total_fixtures`
- `summary.matched`
- `summary.mismatched`
- `summary.errors`

Any mismatch in strict mode exits non-zero and emits one-line mismatch summaries
to stderr.

## API surface gate

The repo also keeps checked-in public API snapshots for `trust-vc`,
`trust-vc-core`, `trust-vc-types`, `trust-vc-merge-contract`,
`trust-vc-merge-runner`, and `trust-vc-trust-engine`. The
`trust-vc-trust-engine` snapshot is the review gate for the compiler-facing
Trust request/report boundary used by tRust integration work.

Check the current surface against the checked-in baselines:

```bash
bash scripts/api_surface_check.sh
```

The script runs on the Trust toolchain: the snapshots are generated from
trustdoc's rustdoc JSON (`targo --unverified rustdoc ... --output-format json`),
and it refuses to run unless `targo` is the Trust targo. The JSON format is
compiler-versioned, so when trustdoc's `format_version` moves, bump
`rustdoc-types` to match and refresh the baselines.

Refresh the checked-in baselines after an intentional, reviewed API change,
then immediately check the refreshed surface:

```bash
bash scripts/api_surface_check.sh --refresh
```

Refreshes are part of the review surface, not generated noise. Only update the
fixtures in the same commit as the intentional public API change they reflect.
