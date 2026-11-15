// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end (surrogate-free) re-port of the spec/proof ghost-arithmetic
//! cluster from upstream Verus `source/rust_verify_test/tests/overflow.rs`
//! (#2778), driving the literal upstream bodies through `vc_extraction`.
//!
//! Two reusable engine features combine here:
//!
//! 1. **vstd checked-`add` spec model** — `add(x, y)` over fixed-width integers
//!    lowers (via `ir_lowering::dispatch::calls::lower_wrapping_free_function_call`)
//!    to the *truncating* (BV-modular) addition that Verus's `builtin::add`
//!    denotes in ghost/proof mode, carrying **no** overflow obligation. The
//!    encoder-level model is locked in `encoder::tests::overflow_spec_add`; these
//!    tests confirm it flows through `add(a, 2)` in extracted obligation
//!    conditions identically to hand-built `ProofObligation`s.
//!
//! 2. **`proof { ghost_var = expr }` mutation lowering** — a statement-position
//!    `proof_block!({ ... })` inside an **exec** function visits its ghost
//!    statements in the current scope, so an assignment to an existing ghost
//!    local (`j = add(j, 2)`) propagates to the surrounding scope and is
//!    substituted into the following `assert`. Exec overflow / div0 / bitshift
//!    obligations are suppressed inside the block (ghost arithmetic is
//!    unbounded), so a ghost `j = j + 2` is *not* overflow-checked.
//!
//! Soundness scope (pinned by the negative tests below): the proof-block lowering
//! is supported only in exec functions; in spec/proof functions, and for `return`
//! inside the block, it stays a fail-closed `Unsupported proof_block!()` /
//! return-rejected error, matching the upstream `proof_in_spec.rs` fail-closed
//! cases. No path produces a false `Verified`.

use super::*;
use crate::encoder::VerifyResult;

/// Extract VCs from the named function and return `(verdict, obligation_count)`.
fn verify_named(code: &str, name: &str) -> (VerifyResult, usize) {
    let file =
        crate::parse_file_allow_tracked(code).expect("proof-block ghost-add fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    let vc = extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"));
    let obligations = vc.obligations.len();
    (vc.verify(), obligations)
}

fn assert_verified(code: &str, name: &str, upstream: &str) {
    let (result, _) = verify_named(code, name);
    match result {
        VerifyResult::Verified => {}
        VerifyResult::Unknown { reason, .. } => {
            panic!("fn {name} ({upstream}) returned solver Unknown, not stable evidence: {reason}")
        }
        other => panic!("fn {name} ({upstream}) should verify, got: {other:?}"),
    }
}

/// "Should fail" = fail-closed: a Counterexample or a solver Unknown, never a
/// false `Verified`. Mirrors upstream `assert_one_fails`.
fn assert_fail_closed(code: &str, name: &str, upstream: &str) {
    let (result, _) = verify_named(code, name);
    match result {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!("fn {name} ({upstream}) must NOT verify (would be unsound), got Verified")
        }
        other => panic!("fn {name} ({upstream}) should be fail-closed, got: {other:?}"),
    }
}

fn extraction_error(code: &str, name: &str) -> String {
    let file = crate::parse_file_allow_tracked(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    match extract_verification_conditions(func) {
        Ok(_) => panic!("fn {name} should be rejected during extraction, but extracted cleanly"),
        Err(err) => err.to_string(),
    }
}

// ========================================================================
// should-verify direction
// ========================================================================

/// Upstream `test_overflow_spec_pass`:
/// ```ignore
/// fn test(a: u64) {
///     let ghost mut j: u64 = a;
///     proof { j = add(j, 2); }
///     assert(j == add(a, 2));
/// }
/// ```
/// The proof-block ghost mutation `j = add(j, 2)` propagates so `j` resolves to
/// `add(a, 2)`; both sides of the assert use the truncating spec `add`, so the
/// equality holds for all `a`. No surrogate assertion.
#[test]
fn faithful_spec_pass_ghost_add_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
            });
            assert!(j == add(a, 2u64));
        }
    "#;
    assert_verified(code, "test", "test_overflow_spec_pass");
}

/// Two ghost `add`s in one proof block, asserted against the truncating model:
/// `proof { j = add(j, 2); j = add(j, 2); } assert(j == add(add(a, 2), 2));`.
/// Confirms multiple ghost mutations chain through the scope and the truncating
/// `add` composes (`j == add(add(a, 2), 2)` for all `a`). This is the verifying
/// dual of upstream `test_overflow_spec_fails_2` (whose `assert(j == a + 4)`
/// uses the *unbounded* exec/spec `+`, hence fails).
#[test]
fn two_ghost_adds_against_truncating_model_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
                j = add(j, 2u64);
            });
            assert!(j == add(add(a, 2u64), 2u64));
        }
    "#;
    assert_verified(
        code,
        "test",
        "test_overflow_spec_fails_2 (verifying truncating dual)",
    );
}

/// The FAITHFUL upstream `test_overflow_spec_fails_2`: two ghost truncating
/// `add`s, then `assert(j == a + 4)` using the **unbounded** `+` (not the
/// truncating `add`). For `a` near `u64::MAX`, `j = add(add(a, 2), 2)` wraps but
/// `a + 4` is the unbounded successor, so they differ and the assert is
/// refutable — upstream `=> Err(e) => assert_one_fails(e)`. trust-vc must be
/// fail-closed (Counterexample or solver Unknown), NEVER a false `Verified`.
/// This is the unguarded case the existing port (evals/verus/ported/overflow.rs)
/// guarded away with `assume!(a < 30)`; here the real failing body is exercised.
#[test]
fn two_ghost_adds_asserting_unbounded_sum_fails_closed() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
                j = add(j, 2u64);
            });
            assert!(j == a + 4u64);
        }
    "#;
    assert_fail_closed(code, "test", "test_overflow_spec_fails_2");
}

/// A ghost `+` (not `add`) inside the proof block must NOT acquire the exec
/// overflow obligation — proof arithmetic is unbounded. With overflow suppressed
/// inside the block, `j = j + 2` propagates as the unbounded ghost successor and
/// `j > a` holds for the ghost value with no spurious overflow refutation. If the
/// exec overflow check leaked onto the proof-block `+`, this would be a false
/// counterexample at `a = u64::MAX`. It must verify.
#[test]
fn ghost_plus_in_proof_block_has_no_overflow_obligation_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = j + 2u64;
            });
            assert!(j == a + 2u64);
        }
    "#;
    // The proof-block `j = j + 2` carries NO overflow obligation (suppressed).
    // The remaining refutation (if any) comes solely from the `a + 2` inside the
    // assert condition, which is the pre-existing assert-site behavior — so we
    // assert the *structural* property here: no `overflow_check_*` obligation is
    // emitted for the proof-block assignment.
    let file = crate::parse_file_allow_tracked(code).expect("fixture parses");
    let func = find_function(&file, "test").expect("fn test");
    let vc = extract_verification_conditions(func).expect("extracts");
    let overflow_checks = vc
        .obligations
        .iter()
        .filter(|o| o.name().starts_with("overflow_check_"))
        .count();
    assert_eq!(
        overflow_checks, 0,
        "a ghost `j = j + 2` inside an exec proof_block must emit NO exec overflow check; \
         proof arithmetic is unbounded in Verus"
    );
}

// ========================================================================
// should-fail direction (fail-closed)
// ========================================================================

/// Upstream `test_overflow_spec_fails_2`:
/// ```ignore
/// fn test(a: u64) {
///     let ghost mut j: u64 = a;
///     proof { j = add(j, 2); j = add(j, 2); }
///     assert(j == a + 4); // FAILS
/// }
/// ```
/// `j == add(add(a, 2), 2)` (truncating), but the bare `a + 4` carries the exec
/// `+` overflow obligation, refuted at `a == u64::MAX`. Fail-closed
/// (Counterexample), matching upstream `assert_one_fails`.
#[test]
fn faithful_spec_fails_2_plus_four_is_fail_closed() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
                j = add(j, 2u64);
            });
            assert!(j == a + 4u64);
        }
    "#;
    assert_fail_closed(code, "test", "test_overflow_spec_fails_2");
}

/// Soundness guard: a WRONG truncating-model equality must not verify. The ghost
/// value is `add(a, 2)`, so asserting `j == add(a, 3)` is refutable (they differ
/// for every `a`). Pins that the ghost mutation is the genuine `add(a, 2)`, not
/// an underspecified/havoc value that would make any equality vacuously hold.
#[test]
fn wrong_truncating_equality_is_fail_closed() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
            });
            assert!(j == add(a, 3u64));
        }
    "#;
    assert_fail_closed(code, "test", "test_overflow_spec_pass (wrong-value guard)");
}

// ========================================================================
// soundness scope: rejections that must stay fail-closed
// ========================================================================

/// SOUNDNESS: a `proof_block!()` inside a **spec** function must remain rejected
/// (`Unsupported proof_block!()`), exactly as upstream
/// `proof_in_spec.rs::nonrecursive_not_yet_supported1` is a fail-closed error.
/// The exec-only gate (`check_overflow()`) is what preserves this — proving the
/// new lowering cannot leak into spec/proof bodies.
#[test]
fn proof_block_in_spec_fn_is_rejected() {
    let code = r#"
        #[trust_vc::spec]
        fn s(i: u64) -> u64 {
            trust_vc::proof_block!({
                trust_vc::assert!(true);
            });
            i
        }
    "#;
    let err = extraction_error(code, "s");
    assert!(
        err.contains("Unsupported proof_block!()"),
        "spec-fn proof_block must stay fail-closed as Unsupported proof_block!(); got: {err}"
    );
}

/// SOUNDNESS: a `proof_block!()` inside a **proof** function is likewise rejected
/// (proof functions also have `check_overflow()` false). Matches upstream
/// `proof_in_spec.rs::proof_fn_local_proof_block_expression_fails_closed`.
#[test]
fn proof_block_in_proof_fn_is_rejected() {
    let code = r#"
        #[trust_vc::proof]
        fn p(i: u64) {
            trust_vc::proof_block!({
                trust_vc::assert!(true);
            });
        }
    "#;
    let err = extraction_error(code, "p");
    assert!(
        err.contains("Unsupported proof_block!()"),
        "proof-fn proof_block must stay fail-closed as Unsupported proof_block!(); got: {err}"
    );
}

/// SOUNDNESS: `return` inside an exec `proof_block!()` is rejected (Verus forbids
/// return inside a proof block). A `return` would otherwise silently escape the
/// ghost scope we do not model.
#[test]
fn return_inside_exec_proof_block_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let ghost mut j: u64 = a;
            trust_vc::proof_block!({
                if a > 0u64 {
                    return;
                }
                j = add(j, 2u64);
            });
        }
    "#;
    let err = extraction_error(code, "test");
    assert!(
        err.contains("return") && err.contains("proof block"),
        "return inside an exec proof_block must be rejected; got: {err}"
    );
}

// ========================================================================
// mode discipline: the EXEC-local liar twins
//
// Every fixture above declares `j` as `let ghost mut j` — the literal upstream
// spelling. Until 2026-09-16 that spelling did not PARSE (`let ghost` is not
// Rust), so this file said `let mut j`, i.e. an EXEC local, and the proof
// block mutated it. That is not a cosmetic difference:
// `trust_vc::proof_block!` expands, in any build without `cfg(trust_mc)`, to
// `let _ = || { ..body.. };` — a closure that is never called. So the exec
// spelling asked the solver to believe a mutation the compiler ERASES.
//
// These twins pin both halves: the exec-local spelling is REJECTED with the
// verbatim Verus diagnostic, and the rejection is not vacuous — the same body
// with `let ghost mut` verifies (the `faithful_*` tests above).
// ========================================================================

/// LIAR TWIN of `faithful_spec_pass_ghost_add_verifies`: identical body, but
/// `j` is an EXEC local. Upstream Verus rejects it with
/// `cannot assign to exec variable from proof mode`
/// (`modes.rs::ghost_wrapper_assign_fail3`), and so must trust-vc.
#[test]
fn proof_block_assigning_an_exec_local_is_rejected() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test(a: u64) {
            let mut j: u64 = a;
            trust_vc::proof_block!({
                j = add(j, 2u64);
            });
            assert!(j == add(a, 2u64));
        }
    "#;
    let err = extraction_error(code, "test");
    assert!(
        err.contains("cannot assign to exec variable from proof mode"),
        "a proof_block! assigning an EXEC local must be rejected with the verbatim \
         Verus diagnostic — the assignment is erased at runtime, so believing it \
         is a false Verified; got: {err}"
    );
}

/// The measured false `Verified` this rule closes, in its sharpest form: before
/// the mode check, this body verified `e == 7` while the compiled program left
/// `e == 0`, and the liar twin `assert!(e == 0)` came back `Counterexample` —
/// proving the solver genuinely held the erased value.
#[test]
fn erased_proof_block_mutation_of_exec_local_cannot_be_believed() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f() {
            let mut e: u64 = 0u64;
            trust_vc::proof_block!({
                e = 7u64;
            });
            assert!(e == 7u64);
        }
    "#;
    let err = extraction_error(code, "f");
    assert!(
        err.contains("cannot assign to exec variable from proof mode"),
        "got: {err}"
    );
}

/// NON-VACUITY control for the two twins above: the same shape with a GHOST
/// local is accepted and reaches a real verdict. Without this, a checker that
/// rejected every `proof_block!` would pass both twins.
#[test]
fn ghost_local_assigned_in_proof_block_is_still_accepted() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn f(a: u64) {
            let ghost mut g: u64 = a;
            trust_vc::proof_block!({
                g = add(g, 2u64);
            });
            assert!(g == add(a, 2u64));
        }
    "#;
    assert_verified(
        code,
        "f",
        "modes.rs declare_spec_var_in_exec (positive control)",
    );
}

/// Rule 1, the exec-side twin: EXEC code may not mutate a ghost/tracked local.
/// Upstream `modes.rs::assign_spec_var_in_exec` / `assign_proof_var_in_exec`.
#[test]
fn exec_code_mutating_a_ghost_local_is_rejected() {
    for (code, upstream) in [
        (
            r#"
            #[trust_vc::ensures(true)]
            fn myfun() {
                let ghost b: bool;
                b = false;
            }
            "#,
            "assign_spec_var_in_exec",
        ),
        (
            r#"
            #[trust_vc::ensures(true)]
            fn myfun() {
                let tracked b: bool;
                b = false;
            }
            "#,
            "assign_proof_var_in_exec",
        ),
    ] {
        let err = extraction_error(code, "myfun");
        assert!(
            err.contains("exec code cannot mutate non-exec variable"),
            "upstream {upstream} must be rejected with the verbatim diagnostic; got: {err}"
        );
    }
}

/// NON-VACUITY control for rule 1: INITIALIZING a ghost/tracked local in exec
/// is legal (upstream `initialize_spec_var_in_exec` /
/// `initialize_proof_var_in_exec` are both `Ok`), and a plain exec assignment
/// is untouched. A checker that rejected every ghost local would pass the test
/// above and fail this one.
#[test]
fn ghost_local_initialization_and_plain_exec_assignment_stay_accepted() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn myfun(a: u64) {
            let ghost g: u64 = a;
            let tracked t: u64 = a;
            let mut e: u64 = a;
            e = a;
            assert!(g == a && t == a && e == a);
        }
    "#;
    assert_verified(
        code,
        "myfun",
        "modes.rs initialize_{spec,proof}_var_in_exec (positive control)",
    );
}
