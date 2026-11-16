# Upstream Verus test suite against a solver or a front end

These scripts run upstream Verus's own prebuilt test binaries, unmodified. The roots come from
`evals/verus/verus-tests.json`: `source/rust_verify_test/tests` and `source/cargo-verus/tests`. A run
changes one of two things:

- **the solver** behind `VERUS_Z3_PATH`, with Verus's own `rust_verify` (`--frontend verus`,
  the default). z3 4.12.5 (Verus's own) is the reference, and ay goes behind the same variable.
  This is **track A**: upstream Verus, unmodified, with ay in place of z3.
- **the front end**: trust-vc's `rust_verify` (crate `trust-vc-rustc`) in the place where the
  harness starts Verus's (`--frontend trust-vc`). No solver process runs; trust-vc answers every
  query in process with ay. Every test is scored against trust-vc's verdict records and against a
  Verus+z3 run of the same suite; see [The trust-vc front end](#the-trust-vc-front-end).

The committed z3 reference set lives in `evals/verus/upstream-suite/`, and the one-line-per-run
ledger of the trust-vc runs in `evals/verus/upstream-suite/runs.csv`.

## Requirements

- **A Verus checkout** at `a40d57c73650cd3648b09386bfdb96ab5c270626` (the `upstream.ref` of
  `evals/verus/verus-tests.json`), built: `source/target-verus/debug/` holds `rust_verify`,
  vstd, the builtin crates and z3 4.12.5, and `source/target.noindex/debug/deps/` holds the
  test binaries for both manifest roots. Build `cargo-verus` tests with `integration-tests`,
  including its `cargo-verus` and `fake-cargo` executables and the matching `.d` files. The
  runner reads the absolute `CARGO_BIN_EXE_*` paths embedded at compilation from those files,
  requires executable helpers, and records/checks their hashes before and after execution.
  Missing harnesses, ambiguous targets, missing helpers or incomplete discovery fail the run.
  Every script finds the checkout as
  `--verus`, else `TRUST_VC_VERUS_PATH`, else `VERUS_PATH`, else `../verus` beside this
  repository (the order `cargo trust-vc evidence` uses). It is only read. After every run
  `run_suite.py` checks that no path under it is newer than the run and that `git status` is
  empty, and records the answer.
- **rustc 1.95.0 from rustup**, a stock-as-oracle (`docs/rulings.md`: kept, pinned, never a
  blocker). `rust_verify` and the test binaries link
  `@rpath/librustc_driver-eea6b8737cd03a8e.dylib` and carry no `LC_RPATH`. The scripts find
  the directory with `RUSTUP_AUTO_INSTALL=0 rustup which --toolchain 1.95.0 rustc`, so nothing
  installs it, and stop with `NOT RUN: oracle rustc 1.95.0 not installed` without it; `--dyld`
  (or `VERUS_SUITE_DYLD`) overrides it. They refuse a directory that does not hold that exact
  file: a `librustc_driver` with another hash does not load, and dyld halts every launch
  (each halt files a macOS crash report). `DYLD_LIBRARY_PATH` must be set on the final `exec`:
  macOS strips `DYLD_*` whenever it passes through a protected binary such as `/bin/sh`,
  `/bin/bash` or `/usr/bin/perl`, so a wrapper has to set it itself (as `run_one.sh` does).
  Without it `rust_verify` dies at launch with `Library not loaded`.
- **Python 3.9 or newer**, or **3.11 or newer when running the first-root Cargo fixtures**
  (`tomllib` reads their internal-skip metadata), standard library only. macOS/APFS for the `cp -c` clones (other
  filesystems fall back to a copy).
- **The ay binary to measure.** `AY_BIN` has **no default** anywhere: every script that runs
  ay refuses without it (`--ay-bin` where a script has that option). The re-run drivers never
  fall back to the `AY_BIN` a run recorded in its `run.json`: that path may hold another build
  by now. A default path once pointed at a stale 0.26.0 build and silently measured the wrong
  solver.

Every output goes under `--out-root` (default `.verus-suite/` at the repository root, which is
gitignored, or `VERUS_SUITE_OUT_ROOT`): `runs/<label>/`, `probes/<label>/`,
`soundness-confirmations.json`.

## Files

| file | what |
|---|---|
| `run_suite.py` | The runner. `--solver PATH --label L` writes `runs/L/{results.csv, summary.md, run.json, bins/, logs/, stage/}`; `--summarize-only` rebuilds the csv and summary from `bins/`. `--frontend trust-vc` runs trust-vc instead, `--capture-diagnostics` keeps every `rust_verify` run's stderr, and every run appends one line to `--ledger` |
| `trust_vc_score.py` | Scores a trust-vc run: verdict records, refusal tags, and the cross-check against the Verus+z3 captures |
| `build_verus_builtins.sh` | Builds upstream's `verus_builtin`, `verus_builtin_macros` and `verus_state_machines_macros` with trustc, for a trust-vc stage |
| `run_one.sh` | One test (or a few) in the stage of an existing label, with shim events and transcripts. It passes every `AY_SHIM_*` and `TOP3_*` variable that is set through to the shim. It exits 2 when it refuses (no stage, no `AY_BIN`, no library) and 0 once the test binary ran; every driver below stops on a refusal instead of recording it as a test outcome |
| `ay_z3shim.py` | The measurement shim (below). Not needed to run the suite |
| `run_tests_with_shim.py` | A list of `binary::test`, one libtest process each, through `run_one.sh` |
| `rerun_tests.py` | Re-run tests of a classified run, each alone, and report the flagged query's answer |
| `rerun_timeouts.py` | The load recheck: every wall-killed INCOMPLETE test again, alone, with a CPU budget |
| `split_rerun.sh` | The 11 pairs of examples that share an event key, re-run one at a time |
| `classify.py` | Classifies every test that is ok on z3 and not ok on the solver under test |
| `confirm_soundness.py` | Re-runs a SOUNDNESS candidate, cuts out the query, asks z3 with MBQI |
| `denominator.py` | Static case count against the tests the binaries contain, and a run's outcomes |
| `suite_common.py` | The path rules above, shared |
| `test_ay_z3shim.py`, `test_harness.py`, `test_trust_vc_score.py` | Offline tests (below) |

## Method

`run_suite.py` builds each test process's environment from scratch and records it in
`runs/<label>/run.json`:

```
VERUS_IN_VARGO=1                     # the harness refuses to run without it (common/mod.rs:242)
RUSTC_BOOTSTRAP=1                    # original Verus frontend only (vargo/libtest setup)
RUST_MIN_STACK=20971520              # vargo sets it
VARGO_TARGET_DIR=<stage>/source/target-verus/debug
DYLD_LIBRARY_PATH=<rustc 1.95.0 lib/>
VERUS_Z3_PATH=<--solver, absolute, symlinks NOT resolved>
VERUS_EXTRA_ARGS=<--verus-extra-args, when given>
HOME USER LOGNAME TMPDIR LANG LC_ALL SHELL PATH   # inherited
<--env K=V ...>
```

The stage, `runs/<label>/stage/`, mirrors what the harness reaches by relative path:

```
stage/examples                          -> <verus>/examples
stage/source/target-verus/debug         -> <verus>/source/target-verus/debug
stage/source/builtin, stage/source/vstd -> <verus>/source/{builtin,vstd}
stage/source/target.noindex/debug/deps/<name>   APFS clone (cp -c) of <name>-<16 hex>
stage/source/rust_verify_test/          cwd of rust_verify_test harnesses
stage/source/cargo-verus/               cwd of cargo-verus harnesses
stage/source/target.noindex/debug/test_inputs/  written by the harness
```

`std::env::current_exe()` names the clone, so the language harness writes its inputs under the
stage. When the first-root `cargo` binary is selected, the stage also gets independent copies
of the checkout's tracked files, including submodule sources, Cargo fixtures and their relative
workspace dependencies. Cargo builds and cleans those copies. The `cargo-verus` integration
harnesses create temporary workspaces and invoke their original compiled helper paths.

Existing `rust_verify_test` binary/test IDs stay unchanged. The second root uses IDs such as
`cargo-verus.test_build::test_name`. Case counts come from each actual libtest discovery stream,
whose completed counts must match the complete unique name set; source anchors are not a roster.

Each binary runs as `<clone> -Z unstable-options --format json --report-time --test-threads 3`,
3 binaries at a time (so at most 9 test processes), largest first. A test running longer than
`--test-stall` (900 s) kills its binary and is recorded as `timeout`; a binary gets `--bin-wall`
(5400 s) in total. After a kill or crash the unfinished tests are re-run with `--exact`, and
when a binary dies with several tests in flight each is re-run alone to find the one that
crashed it. Differences from `vargo test -p rust_verify_test`: 3 test threads per binary
instead of one per core, 3 binaries at once, and cwd is the staged package directory.
Ordinary runs retain the historical `cargo` exclusion and libtest's default ignored behavior.
`--include-ignored` actually executes ignored cases; their declaration never establishes a pass.

Full qualification uses both flags:

```sh
python3 scripts/verus_suite/run_suite.py --solver <solver> --label full-<revision> \
    --full-suite --include-ignored
```

This selects every harness in both roots, including `cargo`, forbids `--only`, `--exclude` and
`--summarize-only`, requires positive discovery for every target, and returns nonzero for any
non-passing case. Coverage policy is recorded with every cache; changing roots, ignored execution
or full-suite selection requires a new label. Every full-suite invocation executes every harness
again, so changing the frontend, builtins or solver cannot reuse earlier passes. Ordinary runs keep
their cache behavior. Old excluded or ignored-only results cannot become new execution evidence.
`run_one.sh` also enables ignored execution for explicitly selected cases.

These are upstream **harness outcomes**. The Cargo integration tests check CLI behavior; a pass
does not establish a solver verdict or proof. The original first-root Cargo body also returns early
for fixture metadata `package.metadata.verus.test_ignore=true`. Source-mapped internal skips are
recorded in `run.json`, each binary's cache, the summary and `results.csv`'s `coverage_note`; their
harness result remains unchanged and they establish no Cargo or solver execution. No upstream
assertion or skip behavior is rewritten.

## The z3 reference

```sh
python3 scripts/verus_suite/run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3-full \
    --full-suite --include-ignored
```

The committed 4,213-case reference and `denominator.py` describe the historical first-root run
with its original exclusions and ignored cases. They do not supply a total for the full two-root
route; use the actual new run's discovery and outcomes.

## The trust-vc front end

```sh
S=scripts/verus_suite; R=$PWD/.verus-suite/runs
targo --unverified build -p trust-vc-rustc --features rustc --bin rust_verify
$S/build_verus_builtins.sh .verus-suite/builtins            # with trustc; rebuild when the toolchain moves
python3 $S/run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3-diags --capture-diagnostics
python3 $S/run_suite.py --frontend trust-vc --rust-verify target/debug/rust_verify \
    --builtins .verus-suite/builtins --reference $R/z3-diags --label trust-vc-<rev> [--only basic]
```

The builtins builder reads exact registry versions from upstream's `source/Cargo.lock`.
It uses `CARGO_HOME`'s source or archive cache; missing archives can be placed in
`OUT_DIR/src/NAME-VERSION.crate` and are checked against the lockfile checksum.
It reports missing sources instead of selecting another cached version. Set
`TRUST_VC_BUILTINS_LINKER` to pass an explicit linker to each Trust compiler invocation.

**Staging.** For `--frontend trust-vc`, `stage/source/target-verus/debug/` is a directory of the
run's own holding `rust_verify` (a clone of `--rust-verify`) and the three builtin crates from
`--builtins`, plus the explicitly selected native Cargo driver pair when supplied: upstream's copies were built by rustc 1.95 and trustc refuses
them (E0514), and a test that imports vstd finds no vstd (trust-vc refuses it with the tag
`vstd`). `VERUS_Z3_PATH` names a path that does not exist, so nothing can reach a z3 by accident,
and `TRUST_VC_VERDICT_DIR` is `runs/<label>/verdicts/`.

For the full two-root Trust measurement, also build the native `verus` target
from the same trust-vc source and select the actual upstream `cargo-verus` build
output:

```sh
targo --unverified build -p trust-vc-rustc --features rustc --bin rust_verify --bin verus
python3 scripts/verus_suite/run_suite.py --frontend trust-vc \
    --rust-verify <actual-rust_verify> --verus-driver <actual-native-verus> \
    --cargo-verus <actual-cargo-verus> --builtins <actual-Trust-builtins> \
    --dyld <actual-Trust-lib> --verus <actual-upstream-cohort> \
    --label <fresh-label> --full-suite --include-ignored
```

Current native drivers that require a GNU scheduler at process entry can use
`--execution-lender <actual-source-built-lend_execution> --threads 1 --parallel-bins 1`
inside an existing fixed build-slot protocol 1 reservation. The selected lender must
retain its zero-token GNU owner until its actual compiler child exits and preserve
that child's exit status and signals. The runner records the selected lender and
Python interpreter identities, stages the lender and original native driver bytes,
and wraps both `rust_verify` and `verus`. The latter remains beside `cargo-verus`
for its unchanged sibling lookup. Diagnostic capture preserves ordinary exit 139
separately from an actual signal.

This lane refuses native epochs, inherited GNU/CPU/SDK advertisements and `--env`
changes to admission context before environment filtering. It runs one harness and
one test thread at a time; a lender grants no additional CPU, SDK, import or proof
authority. The caller's real fixed reservation remains held throughout the suite.
The runner's wrapper tests establish argv, process-status and input-identity
behavior only; actual GNU custody needs a genuine source-built lender and native
compiler execution. Use a fresh label for qualification. Per-binary caches also
bind the staged frontend and lender inputs, so changing them reruns the cases.

`--verus-driver` and `--cargo-verus` are supplied together. Selecting the
first-root `cargo` harness requires them; selecting only the Cargo argument-planning
integration harnesses still uses their compiled-in genuine helpers and their
upstream test fixture named `fake-cargo`. The runner records and rechecks selected
and staged driver bytes. It stages the native `verus` executable beside
`cargo-verus`, preserving that program's exact sibling lookup for `RUSTC_WRAPPER`.
The native entrypoint uses the same linked Trust shim as `rust_verify`, with the
original arguments, environment-based Cargo protocol, macro context and exit
status. It does not run upstream's rustup launcher.

Use the genuine Trust Cargo/compiler paths through `CARGO`, `RUSTC` and `PATH`,
plus an independently owned `CARGO_HOME`, `CARGO_TARGET_DIR` and `TMPDIR`, for
the writable Cargo fixtures. These inputs and the inherited broker CPU reservation
are forwarded to native children and recorded. Native `--env` cannot add bootstrap
or replace compiler/wrapper selection. Inheriting a compiler path transports that
path string; it does not authenticate the compiler or grant an owner. The runner stages no
`libvstd.rlib` or `vstd.vir`; their absence and the native import gate remain
real capability gaps in the resulting cases. Driver staging grants no imported
value, contract, proof or native-code authority. Run without
`--capture-diagnostics` when selecting the direct native executables.

Native Trust runtime selection reads the actual selected harness and engine
Mach-O load commands and requires one consistent driver ABI in the explicit
--dyld directory (or VERUS_SUITE_DYLD). It pins and rechecks that directory's
driver bytes plus selected executable identities. The historical oracle runtime
lookup remains separate. Load names and byte inventories grant no imported value,
contract or proof capability; fresh current-composition build rows still bind
the engine, macros and runtime before a corpus measurement.

**Verdict records.** Every `rust_verify` run appends one JSON line to
`verdicts/<test dir>.jsonl`: every function it saw and its verdict (`verified`, `failed`,
`refused`, `skipped`, `rejected`, `external`, `trusted`), the function's file and line range,
the refusals, and how the run ended. The test dir is the directory of rustc's `-o` output, which
the harness makes per test: `<binary>-<test>`, or `example-<file stem>` for `examples.rs`, whose
entry file lies in the examples tree (two examples can share a stem; records carry the entry
file, which tells them apart).

**Diagnostics capture.** `--capture-diagnostics` puts a bash wrapper in `rust_verify`'s place.
It runs the real binary, passes stdout, stderr, the exit status and a terminating signal through
unchanged, and writes the stderr to `diags/<test dir>/<time>-<pid>.stderr` between an
`entry=<entry file>` and an `exit=<code>` line. A Verus+z3 run captured this way is the
reference for trust-vc runs; the scoring checks that its outcomes match the recorded z3 run
(`evals/verus/upstream-suite/runs/z3/results.csv`) and reports how many differ.

**Scores** (`score.csv`, one row per test, and the summary):

| score | meaning |
|---|---|
| `pass` | the harness passed it, a verdict record exists, nothing was refused, and every function called verified agrees with the reference |
| `refused` | a record or diagnostic carries `trust-vc refused: <tag>`, or a function is recorded refused or skipped. Counted as refused even when the harness passed it (`refused_but_harness_ok`) |
| `false-pass` | the harness passed it without a verdict record. Must be 0 |
| `false-pass-ref` | a function recorded `verified` contains, in the same file, a line where the reference run reports an error (the primary spans of its error diagnostics: the failing assertion, the call whose precondition failed, the failed postcondition, the overflowing operation, or any other error Verus reports there). Must be 0, and wins over every other score |
| `bad-record` | a record line is not JSON. Must be 0 |
| `untagged-fail` | the harness did not pass it and nothing was refused. Must be 0 |
| `vacuous` | the harness passed it without a record, and the reference run captured no `rust_verify` run for it either: the test starts no front end at all (the 7 `examples.rs` files marked `ignore` return at once). Neither a pass nor a failure |

A verified function in a test with no reference capture, or whose capture holds an error with no
primary span, is `unchecked_verified_fns`, which must also be 0. The run is scored ok when all
of these are 0.

**Ledger.** Every run that ran something appends one line to `--ledger` (default
`<out-root>/runs.csv`): label, front end, git head, rust_verify hash, the outcome totals and,
for trust-vc, the score and the reference.

**First launches.** macOS holds the first launch of every new executable file for a scan, which
took about a minute per file under load (measured: 52 s for one fresh clone of a test binary,
27 s for four launched at once). The runner therefore lists the test binaries concurrently, and
re-staging keeps every file whose bytes did not change, so only the first run of a label pays.

## Running ay with NO shim

```sh
mkdir -p .verus-suite/bin && ln -sf "$AY_BIN" .verus-suite/bin/z3
python3 scripts/verus_suite/run_suite.py --solver .verus-suite/bin/z3 --label ay-<rev> \
    --verus-extra-args "-V no-solver-version-check --smt-option timeout=20000"
```

Why this is enough, measured on ay `0919b4e16` and `origin/main` `3211f7fc7` (2026-09-24):

- **A symlink NAMED `z3` turns on ay's z3 mode.** ay switches when its executable file is
  called `z3`; replaying 15 AIR transcripts gave the same stdout as `ay -q --z3-mode` apart
  from timing counters, and `--z3-mode` writes nothing to stderr, so `-q` adds nothing. Setting
  only `argv[0]` (`exec -a z3`, Python's `executable=`) does NOT work. That is why
  `run_suite.py` keeps `--solver` as given and never resolves the symlink.
- **`-V no-solver-version-check`**: ay's z3 mode reports version 5.1.0, and Verus accepts only
  4.12.5 without the flag. `run_suite.py` warns when a solver other than Verus's z3 runs without it.
- **`--smt-option timeout=<ms>`**: ay does not honour Verus's per-query `:rlimit` (it reads it as
  a SAT conflict budget; limits from 100 to 30,000,000 did not stop the stalling query within
  200 s, where z3 stops at 100 in 0.03 s), but it does honour `:timeout`: it answers `unknown`
  with reason `canceled`, AIR reports `Resource limit (rlimit) exceeded` for that one function,
  and the session goes on. `basic::test_short_circuit1` with a 20 s timeout fails cleanly after
  about 20 s (20.2 s measured, and 20.1 s again with this runner on 2026-09-24); behind the
  shim's 60 s wall kill the same test ended in the AIR panic `Got too many empty lines!`. The
  budget is wall-clock and therefore load-sensitive (11 of 844 transcripts of passing tests went
  over 60 s at load about 40, and all answered in 13.7-61.0 s at lower load); the right value
  is an open question.
- **stderr reaches the harness, as it does from z3.** The Verus harness fails a test on any
  non-JSON stderr line (`rust_verify_test/tests/common/mod.rs:209-213`), and AIR does not
  redirect the solver's stderr. ay wrote stderr only in tests that failed anyway: 0 bytes in the
  840 solver processes of the 433 passing tests, and 0 in a replay of all 844 of their
  transcripts. z3 needs it: `triggers::test_trigger_on_lambda_3` passes only when z3's
  `WARNING: pattern does not contain all quantified variables` reaches the harness.
- **`:rlimit-count` needs no rewrite.** AIR subtracts two readings only within one query
  (`air/src/smt_verify.rs:547-548`); ay's counter went down 216 times in 3,169 readings, every
  time at a query boundary.

What still breaks is ay, not the harness: a check-sat ay refuses makes it exit, and `rust_verify`
then aborts with SIGABRT (`panic_in_cleanup`), taking the rest of that test with it. Count those
from the libtest logs (`panic in a destructor during cleanup`), never from macOS crash reports:
ReportCrash keeps a capped, de-duplicated sample.

## The measurement shim, and when to use it

`ay_z3shim.py` stands where z3 would. It is needed only to MEASURE:

- to compare a solver with z3 **query by query**: it logs the sha256 of the whole command
  stream up to every `(check-sat)`, and `classify.py` pairs solver processes by those hashes;
- to cut a query out of a run (transcripts);
- to budget each query in **CPU seconds** rather than wall time on a loaded machine.

| variable | default | what |
|---|---|---|
| `AY_BIN` | none, required | the ay binary |
| `AY_SHIM_ARGS` | `-q --z3-mode` | flags before the caller's `-smt2 -in`; the recorded runs passed the same flags explicitly. Without `--z3-mode` ay answers in its native mode, which AIR does not accept, and `run_suite.py` warns |
| `AY_SHIM_QUERY_WALL_S` | 60 | wall budget per check-sat; the solver is killed past it |
| `AY_SHIM_QUERY_CPU_S` | unset | set: CPU budget per check-sat for the solver's process tree, instead of the wall budget |
| `AY_SHIM_QUERY_WALL_MAX_S` | 900 | the wall backstop in CPU mode |
| `AY_SHIM_EOF_GRACE_S` | 10 | kill a solver still running this long after AIR closed stdin |
| `AY_SHIM_EVENT_DIR` | unset | one JSON line per solver process: answers with durations and prefix hashes, reasons, errors, exit status, stderr tail, kills |
| `AY_SHIM_TRANSCRIPT_DIR` | unset | the exact bytes in each direction, per solver process |
| `SHIM_SOLVER` | `ay` | `z3:<path>` runs that z3 instead, behind the same logging |
| `AY_SHIM_DROP_STDERR` | unset | `1`: keep the solver's stderr from AIR (it is still recorded), as the recorded runs did |
| `AY_SHIM_RLIMIT_MONOTONE` | unset | `1`: rewrite ay's `:rlimit-count` to a monotone counter, as the recorded ay runs did |

The defaults are the end state measured above: stderr is forwarded and recorded, and
`:rlimit-count` passes unchanged. With both opt-outs set, the event log (same keys, same order),
the transcripts, the prefix hashes and the z3 passthrough are those of the shim the recorded
runs used; `test_ay_z3shim.py` checks that against the recorded shims when they are available.

A measured ay run and the z3 events it is paired with:

```sh
S=scripts/verus_suite; R=$PWD/.verus-suite/runs
python3 $S/run_suite.py --solver $S/ay_z3shim.py --label ay-<rev> \
    --verus-extra-args "-V no-solver-version-check" --bin-wall 10800 \
    --env AY_BIN=$AY_BIN --env "AY_SHIM_ARGS=-q --z3-mode" --env AY_SHIM_QUERY_WALL_S=60 \
    --env AY_SHIM_EVENT_DIR=$R/ay-<rev>/events
python3 $S/run_suite.py --solver $S/ay_z3shim.py --label z3-shim \
    --verus-extra-args "-V no-solver-version-check" \
    --env SHIM_SOLVER=z3:<verus>/source/target-verus/debug/z3 --env AY_SHIM_QUERY_WALL_S=120 \
    --env AY_SHIM_EVENT_DIR=$R/z3-shim/events
AY_BIN=$AY_BIN $S/split_rerun.sh ay-<rev>             # the 11 example pairs, one at a time
AY_BIN=$AY_BIN python3 $S/confirm_soundness.py --label ay-<rev>   # only if classify finds SOUNDNESS rows
python3 $S/classify.py --label ay-<rev>
```

The two runs must use the same `VERUS_EXTRA_ARGS`: `--smt-option timeout=...` adds a
`set-option` line to the stream and so changes every prefix hash. `classify.py` reads the
reference outcomes from `runs/z3/bins/` or, for a committed reference that keeps only
`results.csv`, from `runs/z3/results.csv`.

## Reproducing the recorded 2026-09-23 runs

The runs were recorded on an Apple M2 Max (12 cores, 32 GiB, macOS 26.6.2) with Python 3.9.6,
while other jobs loaded the machine (load about 9 during the z3 run, 10 to 51 during the ay run).
They used the shim with stderr dropped and the rlimit rewrite on, so pass both opt-outs:

```sh
S=scripts/verus_suite; R=$PWD/.verus-suite/runs; Z3=<verus>/source/target-verus/debug/z3
python3 $S/run_suite.py --solver $Z3 --label z3                  # 215.2 s; a repeat matched test for test
python3 $S/run_suite.py --solver $S/ay_z3shim.py --label z3-shim --verus-extra-args "-V no-solver-version-check" \
    --env SHIM_SOLVER=z3:$Z3 --env AY_SHIM_EVENT_DIR=$R/z3-shim/events --env AY_SHIM_QUERY_WALL_S=120 \
    --env AY_SHIM_DROP_STDERR=1
python3 $S/run_suite.py --solver $S/ay_z3shim.py --label ay-0919b4e16 --verus-extra-args "-V no-solver-version-check" \
    --env AY_BIN=<ay 0919b4e16> --env "AY_SHIM_ARGS=-q --z3-mode" --env AY_SHIM_QUERY_WALL_S=60 \
    --env AY_SHIM_EVENT_DIR=$R/ay-0919b4e16/events --env AY_SHIM_DROP_STDERR=1 --env AY_SHIM_RLIMIT_MONOTONE=1 \
    --bin-wall 10800                                            # 7,521 s at load 10-51
AY_BIN=<ay 0919b4e16> AY_SHIM_DROP_STDERR=1 AY_SHIM_RLIMIT_MONOTONE=1 $S/split_rerun.sh ay-0919b4e16
AY_BIN=<ay 0919b4e16> AY_SHIM_DROP_STDERR=1 AY_SHIM_RLIMIT_MONOTONE=1 python3 $S/confirm_soundness.py --label ay-0919b4e16
python3 $S/classify.py --label ay-0919b4e16
AY_BIN=<ay 0919b4e16> AY_SHIM_DROP_STDERR=1 AY_SHIM_RLIMIT_MONOTONE=1 python3 $S/rerun_timeouts.py \
    --label ay-0919b4e16 --out $R/ay-0919b4e16/timeout-rerun --jobs 9   # the load recheck, 60 CPU s per query
```

Recorded results:

- **z3 4.12.5**: 4,213 tests; 4,114 ok; 0 FAILED, 0 timeout, 0 crashed; 80 ignored (62
  `#[ignore]`, 18 `integer_ring.rs` cases that need `singular`); 19 not-run (`cargo.rs`). The
  comparison set for another solver is the 4,114. Behind the shim with stderr dropped, z3 was
  4,113 ok and 1 FAILED (`triggers::test_trigger_on_lambda_3`, which needs z3's stderr).
- **ay `0919b4e16`**: 2,040 of the 4,114 ok: 1,606 never start a solver, 433 give every answer
  z3 gives, and 1 (`test_trigger_on_lambda_3`) accepts any `Err`. 2,074 not ok: SOUNDNESS 0
  (the one candidate was refuted: z3 with MBQI also proves it), SOLVER-ERROR 1,135 (the
  unsupported-logic refusal and exit), INCOMPLETE 928, PROTOCOL 0, OTHER 11. No test was ok on
  ay and not ok on z3, and ay never answered `sat`. The load recheck with 60 CPU s per query
  moved 2 more tests to ok (2,042).

`test_harness.py` checks, when `VERUS_BASELINE_ROOT` points at the recorded run tree, that
`classify.py` reproduces its `classified.csv`, `query-diff.csv`, `ok-breakdown.csv` and
`classified.md` byte for byte, and that `denominator.py` reproduces its `denominator.csv`.

## Provenance

- **Verus** `a40d57c73650cd3648b09386bfdb96ab5c270626` (`target-verus/debug/version.txt`:
  `0.2026.04.27.a40d57c`, artifacts built 2026-09-16). The sha256 of the frontend, vstd, the
  builtin crates, z3 and the rustc driver are in `evals/verus/upstream-suite/target-verus.sha256`
  (names relative to `<verus>/source/target-verus/debug`, the driver under rustup's 1.95.0
  toolchain); the 129 test binaries are in `test-binaries.sha256`.
- **z3** 4.12.5, Verus's own `target-verus/debug/z3`, sha256
  `bbb24b8fed27552f7fb7cfdf0ed9101e6e24fd0cc0b9cfb945233b3f2ed333c5`.
- **ay** `0919b4e1615aacd3bbe78f4cc2070aed50048724` (on ay's `origin/main`),
  `ay 0.27.0+build.10797.0919b4e1615aacd3bbe78f4cc2070aed50048724@2026-09-24T01:45:21Z`,
  sha256 `2f085c47a7c787e2eb61fc6f3678eb6f3d1cf3d6170c14371d2aa3e62464fe9b`. Built with
  `targo --unverified build --release -p ay --bin ay --features cli` with Trust verification
  off for every unit, on `rustc 1.99.0-dev (321aaeda7 2026-09-17)`. A rebuild is not
  byte-identical: the version string embeds the build time.
- **rustc** 1.95.0 (59807616e 2026-04-14), `librustc_driver-eea6b8737cd03a8e.dylib` sha256
  `d41766d9ed6e9c7959eeb7678b9a6bb301f70948664cd39a8a0d2d83ad23d54e`.

## Where the fixes are tracked

The root causes of ay's 2,074 failures, ranked as a fix queue with reproducers, the measured
number of tests each fix unblocks, and the fix-simulation shim and root-cause tools behind those
numbers, are to live in ay as `docs/z3-parity/2026-09-23-diagnoses-verus-suite.md`. **Pending:**
as of 2026-09-24 that file is only on ay's local, unmerged branch `land/verus-suite-docs`
(`97c00ae84`), not on ay's `main`.

That branch's fix-simulation shim (`docs/z3-parity/2026-09-23-verus-suite/tools/ay-z3shim-top3`)
needs `AY_BIN` **and** `TOP3_Z3` (z3 4.12.5, `<verus>/source/target-verus/debug/z3`) and exits
at once without either, which makes `rust_verify` abort with SIGABRT at its first query.
`run_one.sh` passes every `TOP3_*` variable through (`TOP3_Z3`, and `TOP3_ORACLE` when set), so
`SHIM=<that shim> TOP3_Z3=<verus z3>` works with the drivers here; `test_harness.py` checks that
both variables reach the test binary.

## Tests

```sh
python3 -m unittest scripts/verus_suite/test_ay_z3shim.py scripts/verus_suite/test_harness.py \
    scripts/verus_suite/test_trust_vc_score.py
VERUS_BASELINE_ROOT=<recorded run tree> python3 -m unittest scripts/verus_suite/test_harness.py
```

They are offline and take seconds. Without `VERUS_BASELINE_ROOT` the reproduction checks and the
comparison with the recorded shims are skipped; the denominator check also needs the Verus
checkout and rustc 1.95.0.
