//! Quickstart for the trust_vc MACRO API (annotation-based contracts).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The other examples in this directory drive the verifier through the low-level
//! `VerificationContext` API (Path A: declare variables, push assumptions and
//! assertions by hand). This example shows the *high-level* surface the README
//! advertises: you annotate ordinary Rust functions with trust_vc's contract
//! macros — preconditions (`requires`), postconditions (`ensures`), and the
//! return-value binder (`returns`) — and trust_vc extracts the proof obligations
//! straight from the source and discharges them with ay.
//!
//! We use the `#[trust_vc::contract(...)]` attribute form here because it compiles
//! cleanly as an ordinary runnable binary. The README also shows the body-macro
//! spelling for the same contracts:
//!
//! ```ignore
//! #[trust_vc::proof]
//! fn increment(x: i32) -> i32 {
//!     trust_vc::requires!(x < 2147483647);
//!     trust_vc::ensures!(result > x);
//!     x + 1
//! }
//! ```
//!
//! Both spellings encode the same `requires`/`ensures` contract; the verifier
//! reads either form syntactically.
//!
//! How verification happens here: `trust_vc_core::verify_function_from_file` parses
//! THIS source file, finds the annotated function by name, builds its verification
//! conditions from the contract clauses and the function body, and sends them to
//! ay. We point it at our own path via `file!()` so the example is self-contained.
//!
//! ```bash
//! targo --unverified run -p trust-vc --example proof_macro_quickstart
//! ```

use trust_vc_core::{verify_function_from_file, VerifyResult};
// `nat` is trust_vc's non-negative unbounded spec integer. At the Rust type
// level it is provided by trust-vc-types; the verifier reads the `nat` type name
// from the source and models it as an unbounded `>= 0` integer (Verus `nat`).
use trust_vc_types::nat;

// ---------------------------------------------------------------------------
// Functions carrying trust_vc contracts.
//
// `requires(...)` states a precondition, `ensures(...)` a postcondition, and
// `returns(result)` names the returned value so the postcondition can refer to
// it. These contracts are what trust_vc reads to build the proof obligations.
// ---------------------------------------------------------------------------

/// `result == x + 1` grows the input — provable over `i32` once we forbid the
/// single overflowing input (`x == i32::MAX`) with a precondition. This is the
/// idiomatic way to state a fact about a bounded machine integer: name the guard
/// that rules out wraparound, exactly as you would in Verus.
#[trust_vc::contract(
    requires(x < 2147483647),
    ensures(result > x),
    returns(result),
)]
fn increment(x: i32) -> i32 {
    x + 1
}

/// Doubling a positive value stays positive — stated over `nat` (Verus's
/// unbounded non-negative integer) so the README-style claim `x + x > x` holds
/// without a machine-width overflow guard.
#[trust_vc::contract(
    requires(x > 0),
    ensures(result > x),
    returns(result),
)]
fn double_positive(x: nat) -> nat {
    x + x
}

/// A pure precondition/postcondition relationship with no body arithmetic risk:
/// if `n >= 0` then the returned value equals `n`.
#[trust_vc::contract(
    requires(n >= 0),
    ensures(result == n),
    returns(result),
)]
fn identity(n: i32) -> i32 {
    n
}

// ---------------------------------------------------------------------------
// Driver: verify each contracted function and report ay's verdict.
// ---------------------------------------------------------------------------

/// This example's own source path. We resolve it against `CARGO_MANIFEST_DIR`
/// (the crate directory, known at compile time) rather than using a bare
/// `file!()`, so verification works no matter the current working directory.
fn source_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/proof_macro_quickstart.rs")
}

fn report(path: &str, name: &str) -> bool {
    // trust_vc re-reads the annotated functions above and verifies the named one.
    match verify_function_from_file(path, name) {
        Ok(VerifyResult::Verified) => {
            println!("  ✓ {name}: Verified");
            true
        }
        Ok(VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        }) => {
            println!("  ✗ {name}: Counterexample for {obligation_name}: {model:?}");
            false
        }
        Ok(other) => {
            println!("  ? {name}: {other:?}");
            false
        }
        Err(err) => {
            println!("  ! {name}: extraction error: {err}");
            false
        }
    }
}

fn main() {
    println!("trust_vc Macro API Quickstart");
    println!("=============================");
    println!("Annotated functions are verified from source via ay.\n");

    let path = source_path();
    let path = path.to_str().expect("example path should be valid UTF-8");
    let mut all_ok = true;
    for name in ["increment", "double_positive", "identity"] {
        all_ok &= report(path, name);
    }

    println!(
        "\n{}",
        if all_ok {
            "All contracted functions verified."
        } else {
            "Some contracted functions did not verify (see above)."
        }
    );

    println!("\nKey points:");
    println!("- Annotate with #[trust_vc::contract(requires(..), ensures(..), returns(..))]");
    println!("  (or the body-macro forms requires!(..) / ensures!(..) under #[trust_vc::proof]).");
    println!("- Bounded ints (i32/u64) carry overflow semantics: guard wraparound");
    println!("  with a precondition, or model the claim over int / nat.");
    println!("- ay checks each obligation by refutation: no counterexample => Verified.");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn macro_quickstart_functions_verify() {
        let path = source_path();
        let path = path.to_str().expect("example path should be valid UTF-8");
        for name in ["increment", "double_positive", "identity"] {
            let r = verify_function_from_file(path, name);
            assert!(
                matches!(r, Ok(VerifyResult::Verified)),
                "{name} should verify via the macro API, got {r:?}"
            );
        }
    }
}
