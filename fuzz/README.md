# False-Verified Fuzz Suite

This directory contains the `cargo-fuzz` harnesses for issue `#2736`.
Each target generates a Rust function with a contradictory postcondition and
panics only if TrustVc reports `VerifyResult::Verified`.

## Prerequisite

```bash
targo install cargo-fuzz
```

## Smoke Test

Run the deterministic regression tests for the generator and oracle:

```bash
targo test --manifest-path fuzz/Cargo.toml
```

## Individual Targets

```bash
targo fuzz run ensures_false -- -max_total_time=60
targo fuzz run strict_inequality -- -max_total_time=60
targo fuzz run mode_crossing -- -max_total_time=60
targo fuzz run collections_contradiction -- -max_total_time=60
```

## 1-Hour Sweep

Run each target for 15 minutes from the repository root:

```bash
targo fuzz run ensures_false -- -max_total_time=900
targo fuzz run strict_inequality -- -max_total_time=900
targo fuzz run mode_crossing -- -max_total_time=900
targo fuzz run collections_contradiction -- -max_total_time=900
```

Any libFuzzer crash from these harnesses is a soundness bug: the target only
panics when a contradictory program comes back `Verified`.
