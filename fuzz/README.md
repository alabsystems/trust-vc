# False-Verified Fuzz Suite

This directory contains the libFuzzer harnesses for issue `#2736`.
Each target generates a Rust function with a contradictory postcondition and
panics only if TrustVc reports `VerifyResult::Verified`.

## Toolchain: the Trust toolchain, through `fuzz/run.sh`

`fuzz/run.sh <target> [libFuzzer args]` builds one target with
`targo --unverified build --release --target <host>` and cargo-fuzz's `-s none`
coverage instrumentation (sancov-module, inline 8-bit counters, pc-table,
trace-compares, `--cfg fuzzing`, debug assertions, overflow checks), then runs
it on `fuzz/corpus/<target>` and writes crashes to `fuzz/artifacts/<target>/`
(both gitignored). The fuzz binaries are test harnesses, so the unverified lane
is the right one: it carries no proof claim. `targo trust-vc fuzz` runs the
same script.

Two things it deliberately does not do:

- It does not go through cargo-fuzz. `targo fuzz` is not a command, and
  cargo-fuzz 0.13.2 spawns a bare `cargo` from PATH (`src/project.rs`,
  `Command::new("cargo")`), not `$CARGO`, so its build would leave both Targo
  lanes.
- It enables no sanitizer. The Trust sysroot ships no sanitizer runtime
  (measured 2026-09-28 on trustc 321aaeda7: `ld: library
  'rustc-trust_rt.asan' not found`). The harnesses are safe Rust whose failure
  signal is a panic, which libFuzzer reports without one.

## Smoke Test

Run the deterministic regression tests for the generator and oracle:

```bash
targo --unverified test --manifest-path fuzz/Cargo.toml
```

## Individual Targets

From the repository root:

```bash
fuzz/run.sh ensures_false -max_total_time=60
fuzz/run.sh strict_inequality -max_total_time=60
fuzz/run.sh mode_crossing -max_total_time=60
fuzz/run.sh collections_contradiction -max_total_time=60
```

## 1-Hour Sweep

Run each target for 15 minutes from the repository root:

```bash
fuzz/run.sh ensures_false -max_total_time=900
fuzz/run.sh strict_inequality -max_total_time=900
fuzz/run.sh mode_crossing -max_total_time=900
fuzz/run.sh collections_contradiction -max_total_time=900
```

Any libFuzzer crash from these harnesses is a soundness bug: the target only
panics when a contradictory program comes back `Verified`.

## STOCK EXCEPTION: an AddressSanitizer build

Only an AddressSanitizer build needs a stock toolchain, because that is the
runtime the Trust sysroot lacks. It is an explicit exception, never a fallback:
`<nightly>` is a dated stock nightly that `rustup toolchain list` already shows,
and `RUSTUP_AUTO_INSTALL=0` makes a missing one an error instead of a download.

```bash
# STOCK EXCEPTION (ASan only; Trust lacks sanitizer runtimes: `ld: library 'rustc-trust_rt.asan' not found`)
export RUSTUP_AUTO_INSTALL=0
rustup run <nightly> cargo install cargo-fuzz
rustup run <nightly> cargo fuzz run ensures_false -- -max_total_time=60
```
