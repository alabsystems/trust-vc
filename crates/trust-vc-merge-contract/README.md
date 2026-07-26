# trust-vc-merge-contract

Versioned merge-boundary schema for trust_vc to trust_mc handoff.

## Version policy

- Current schema: `MergeBundle` v3 (`bundle_version = 3`)
- Supported versions: 1 through 3 (inclusive).
- v3 bundles include an explicit `expression_format` field
  (`smt_lib2_term_v1`) declaring the grammar of `TypedExpr.expr` strings.
- Unsupported versions are hard-fail:
  `MergeBundle::from_json_str` returns `MergeBundleError::UnsupportedBundleVersion`
  for versions outside the supported range.

This fail-closed behavior is intentional so trust_vc and trust_mc do not silently
accept incompatible bundle layouts.

## Expression format

v3 bundles use `expression_format: smt_lib2_term_v1`, meaning every
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

Refresh the checked-in baselines after an intentional, reviewed API change:

```bash
targo run -p trust-vc-merge-contract --bin generate_api_surface_fixtures
```

Refreshes are part of the review surface, not generated noise. Only update the
fixtures in the same commit as the intentional public API change they reflect.
