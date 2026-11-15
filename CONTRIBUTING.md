# Contributing to trust-vc

## Overview
trust-vc is a formal verification tool for Rust, created by Andrew Yates. This guide explains how to contribute.

## Repository Structure
```
crates/
  trust-vc/           — Proc macros (count them, do not quote a number:
                        `grep -c '^#\[proc_macro' crates/trust-vc/src/lib.rs`)
  trust-vc-core/      — Verification engine
  trust-vc-types/     — Ghost types (Seq, Set, Map, etc.)
  trust-vc-std/       — Verified lemma specifications
  cargo-trust-vc/     — CLI tool (cargo trust-vc check)
  trust-vc-merge-*    — MergeBundle handoff to Trust's unified verifier
```

## Development Setup
```bash
git clone <repo>
cd trust-vc
targo --unverified build
targo --unverified test
```

## Running Tests
```bash
# Full test suite
targo --unverified test

# Single crate
targo --unverified test -p trust-vc-core

# Specific test
targo --unverified test -p trust-vc-core boundary_i32

# With expensive tests
targo --unverified test --features expensive-tests
```

## Writing Tests
Tests use the VerificationContext API:
```rust
let mut ctx = VerificationContext::new();
ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
ctx.push_obligation(ProofObligation::assert("name", "x > 0"));
let result = AYEncoder::verify(&ctx);
expect_verified(&result, "description");
```

Available result oracles: expect_verified, expect_not_verified, expect_counterexample, expect_error, expect_unknown, expect_fail_closed, expect_verified_or_unknown.

## Code Style
- Follow Rust standard formatting with the Trust toolchain: `targo fmt --all`
  (`targo fmt --all --check` to gate) and lint with
  `targo tippy --locked --workspace --all-targets -- -D warnings`. Never bare
  `cargo fmt` / `cargo clippy`: those names resolve to a stock toolchain.
- 500 line max per file
- pub(crate) by default; pub only for crate API
- Use thiserror for error types
- No unwrap() in production code

Run the repository audit before submitting changes:
```bash
python3 scripts/quality_audit.py
```

Use `--max-rust-lines N` or `QUALITY_AUDIT_MAX_RUST_LINES=N` when intentionally
checking a different file-size threshold. Test, example, bench, and fuzz code is
excluded from the production unwrap/expect/panic/todo policy unless
`--strict-tests` is passed.

There is **no CI** in this repository — no `.github/workflows`, nothing runs on
push. Every gate above is a local script you must run yourself. The fast subset,
which is the one worth running on every change, is:
```bash
python3 scripts/quality_audit.py --skip-rust-size --skip-production-policy
```
Either run can report findings that already exist on `main` (home paths quoted
inside internal, unexported receipts; the size and production-policy backlogs).
Compare against `main` before assuming you broke something — and do not add
new ones.

## Commit Messages
- Include what changed, why, and test results
- Reference issue numbers (#N)

## Architecture Overview
See README.md for the pipeline overview and `design-trust-proof-backend.md` for the design.

## Adding a New Lemma to trust-vc-std
1. Choose the right module (seq.rs, set.rs, map.rs, arithmetic.rs)
2. Add a pub fn with a doc comment describing the property
3. Use stub body: `let _ = (args,);`
4. Ensure `targo --unverified check --tests` passes

## Adding a New Test
1. Choose the right test module (regression_*.rs for regression tests)
2. Follow the existing pattern
3. Use result oracles (expect_verified, etc.)
4. Run `targo --unverified test` to verify

## Questions?
Open an issue or contact Andrew Yates <andrewyates.name@gmail.com>.

Copyright 2026 Andrew Yates Author: Andrew Yates <andrewyates.name@gmail.com>. Apache 2.0.
