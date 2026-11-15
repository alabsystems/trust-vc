# Upstream Verus test suite: the z3 reference set

What upstream Verus's own test suite does with its own solver. Verus
`a40d57c73650cd3648b09386bfdb96ab5c270626` (the `upstream.ref` of `../verus-tests.json`), its
prebuilt `rust_verify_test` binaries unmodified, and z3 4.12.5 behind `VERUS_Z3_PATH`, recorded
2026-09-23 by `scripts/verus_suite/run_suite.py`. It is the reference a solver put behind the
same variable is compared with (track A: ay in place of z3); `scripts/verus_suite/README.md`
has the method, how to run it, and the provenance of every binary.

Fresh discovery on 2026-11-10 covers both maintained manifest roots and records
4,261 cases in 135 harnesses: 4,213 from `rust_verify_test` and 48 from
`cargo-verus`. The 80 ignored cases and 19 first-root Cargo cases remain required
work. `discovery-2026-11-10-cases.json` preserves every discovered name, location
and ignore declaration; `discovery-2026-11-10.json` records its provenance and
scope. No body was executed by this discovery. Other target/feature configurations
remain part of the full goal. The reference comparison below retains its original
4,114-case selection and does not define completion of that goal.

| file | what |
|---|---|
| `runs/z3/results.csv` | one row per test: binary, source file, name, line, outcome, time, message, detail |
| `runs/z3/summary.md` | totals, per-file table, the tests that are not ok |
| `excluded-from-comparison.csv` | the historical reference's tests that are not `ok` on z3, with the reason: `#[ignore]` in source, `cfg_attr(not(feature = "singular"), ignore)`, or `cargo.rs` not run. They were left out of that comparison; they remain in the full goal |
| `denominator.md`, `denominator.csv` | the static case count of `rust_verify_test/tests/*.rs` reconciled with the tests the binaries contain, with every difference explained |
| `target-verus.sha256` | sha256 of the frontend, vstd, the builtin crates, z3 and the rustc 1.95.0 driver the runs used |
| `test-binaries.sha256` | sha256 of the 129 test binaries |
| `runs.csv` | one line per run of `run_suite.py` with this file as `--ledger`: the Verus+z3 capture used as reference, and every trust-vc run (below) |
| `runs/trust-vc/score.csv` | the whole-suite trust-vc run of the last ledger line: one scored row per test |

The binaries contain 4,213 tests. On z3: 4,114 ok, 0 FAILED, 0 timeout, 0 crashed, 80 ignored,
19 not run. **That historical solver comparison uses those 4,114 tests.**

How it was produced, and how to check it again:

```sh
python3 scripts/verus_suite/run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3
python3 scripts/verus_suite/run_suite.py --label z3 --summarize-only    # results.csv, summary.md
python3 scripts/verus_suite/denominator.py --results evals/verus/upstream-suite/runs/z3/results.csv \
    --out-dir evals/verus/upstream-suite                                 # denominator.md, .csv
```

`results.csv` here is byte for byte the recorded run's; `summary.md` and `denominator.md` are
what the landed tools write from the recorded run (the only difference from the files written
that day: home paths shown as `~` or `<verus>`). The CSV files keep the CRLF row ends Python's
`csv` module writes (`.gitattributes`). `scripts/verus_suite/test_harness.py` checks that the
three tables agree with each other.

## trust-vc runs

The same binaries run with trust-vc's `rust_verify` (crate `trust-vc-rustc`) in place of Verus's
(`run_suite.py --frontend trust-vc`, method in `scripts/verus_suite/README.md`). Every test is
scored against trust-vc's verdict records and against a Verus+z3 run of the same suite made with
`--capture-diagnostics` (label `z3-diags` in `runs.csv`; its outcomes equal `runs/z3/results.csv`
test for test). A pass needs the harness to pass, a verdict record, no refusal, and every function
trust-vc calls verified free of any line where Verus+z3 reports an error. A run is ok when there
is no false pass of either kind, no untagged failure, and no verified function left unchecked.

`runs.csv` holds the totals of each run; `runs/trust-vc/score.csv` the per-test scores of the
latest whole-suite run. The capture itself (about 19 MB of stderr) is not committed: rerun it
with `run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3-diags
--capture-diagnostics`.

## What this is NOT

- **Not the syn-lane corpus coverage.** The trust-vc runs above measure the compiler-integrated
  front end on the unmodified suite; the syn lane's headline is
  `scripts/corpus_coverage.py --gate-json`, and its corpus manifest is `../verus-tests.json`.
- Not a result for ay. The ay runs, their event logs and their classification stay outside
  git; the ledger (`docs/ledger.md`) records their headline. The fix queue lives in ay as
  `docs/z3-parity/2026-09-23-diagnoses-verus-suite.md`.
- Not the whole upstream suite: `cargo.rs` (19 tests) shells out to `cargo` builds and is not
  run, and the `singular` feature was off, as in the prebuilt set.
