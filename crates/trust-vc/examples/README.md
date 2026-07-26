# TrustVc Examples

This directory contains examples demonstrating the Path A verification approach using direct VerificationContext API.

## Architectural Note

After the architectural pivot (#397), all Path B examples (macro-based) have been removed. The current examples demonstrate the Path A pattern which directly uses the VerificationContext API for verification.

## Examples

### proof_macro_quickstart.rs
The high-level **macro API** quickstart that the top-level README advertises:
annotate ordinary functions with `#[trust_vc::contract(requires(..), ensures(..),
returns(..))]` and let trust_vc extract and discharge the proof obligations. Each
contracted function is verified from source via `verify_function_from_file`.

```bash
targo run --example proof_macro_quickstart
```

### path_a_migration_guide.rs
Shows how to convert from the broken Path B (macro) approach to the working Path A (explicit API) approach. Includes examples of assertions, preconditions, postconditions, and termination.

```bash
targo run --example path_a_migration_guide
```

### path_a_verification.rs / basics_path_a.rs / binary_search_path_a.rs / termination_path_a.rs
Demonstrate verification through ay using the `VerificationContext` API directly.

```bash
targo run --example path_a_verification
targo run --example basics_path_a
targo run --example binary_search_path_a
targo run --example termination_path_a
```

## Integer model note (important)

trust_vc models `i32` / `u32` / `u64` as **bitvectors with wraparound**, exactly
like the machine. So mathematical-looking claims such as `x > 0 ==> x + 1 > x` are
genuinely *false* at the type boundary (`x == i32::MAX` wraps to a negative
result) and ay correctly reports the counterexample — the verifier is not wrong,
the claim is. To state a fact about mathematical integers, either:

- model it over `int` / `nat` (Verus's unbounded spec integers), or
- add the precondition that rules out overflow (e.g. `requires(x < i32::MAX)`).

Two other practical limits the examples stay within: ay is a *decision procedure
for linear* integer arithmetic, so obligations that multiply or divide two
unknowns (nonlinear) can come back `Unknown` or time out. Where an example needs
division, it divides by a constant; where it needs a measure, it uses a linear
one. Each such spot carries a `SUPPORTED-FRAGMENT NOTE` comment.

## Key Differences from Path B

Path A requires:
- Explicit variable declaration with `ctx.declare_var()`
- Using `ctx.add_assume()` instead of `requires!()`
- Using `ctx.add_assert()` instead of `trust_vc::assert!()`
- No thread-local state or RefCell issues
- Direct control over verification context

## Running Examples

```bash
# Run migration guide
targo run --example path_a_migration_guide

# Run verification demo
targo run --example path_a_verification

# Check compilation
targo check --examples

# Run tests
targo test --examples
```