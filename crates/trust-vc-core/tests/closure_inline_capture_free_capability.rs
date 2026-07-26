// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A BARE `let f = |params| body` closure applied by name `f(args)` is now
//! INLINED at the call site when its body is a PURE function of its parameters
//! (no captured outer locals, no free callees): `f(args)` models as the body
//! with each parameter substituted by its argument. So `let f = |y| y + 1; f(x)`
//! models as `x + 1` and `ensures(result == x + 1)` VERIFIES — previously it
//! failed closed with "unknown return type for function 'f'" (bare closures got
//! no `SpecFn` type, unlike `closure!` literals / `Fn`-bound params).
//!
//! SOUNDNESS (the load-bearing part): the inline is an EXACT value substitution
//! only for a CAPTURE-FREE body — the closure IS its body applied to the args,
//! independent of move/non-move capture semantics. A captured outer variable
//! (the mutation-capture false-verify class) or a free callee makes the body's
//! referenced-ident set exceed its params, so the inline is declined and the
//! call stays fail-closed (sound over-rejection). A false ensures must still
//! COUNTEREXAMPLE (not vacuously verify), and the invoked body's arithmetic
//! panic-freedom (divide-by-zero) is still pinned by the independent
//! arith-safety path.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!(
        "tvc_clos_inline_{}_{}.rs",
        std::process::id(),
        name
    ));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// CAPABILITY: identity closure applied — result == x. Must VERIFY.
const ID_TRUE: &str = r#"
#[trust_vc::ensures(result == x)]
fn t(x: u32) -> u32 { let f = |y: u32| y; f(x) }
"#;

// CAPABILITY: +1 (overflow-guarded) — result == x + 1. Must VERIFY.
const ADDONE_TRUE: &str = r#"
#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + 1u32)]
fn t(x: u32) -> u32 { let f = |y: u32| y + 1u32; f(x) }
"#;

// CAPABILITY: a param used TWICE substitutes both occurrences — result == x + x.
const TWICE_TRUE: &str = r#"
#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + x)]
fn t(x: u32) -> u32 { let f = |y: u32| y + y; f(x) }
"#;

// SOUNDNESS: the closure adds 1 but the postcondition claims result == x. Must
// COUNTEREXAMPLE (the inline models the REAL body — no vacuous verify).
const ADDONE_FALSE: &str = r#"
#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x)]
fn t(x: u32) -> u32 { let f = |y: u32| y + 1u32; f(x) }
"#;

// SOUNDNESS: closure returns a constant 0, postcondition claims result == x for
// x == 5. Must COUNTEREXAMPLE.
const CONST_FALSE: &str = r#"
#[trust_vc::requires(x == 5u32)]
#[trust_vc::ensures(result == x)]
fn t(x: u32) -> u32 { let f = |_y: u32| 0u32; f(x) }
"#;

// SOUNDNESS (CARDINAL): the body captures an outer local `a`. The inline is
// DECLINED (referenced ident `a` is neither a param nor body-bound), so the call
// stays fail-closed — a WRONG postcondition (result == x + 999) must NOT verify.
const CAPTURE_WRONG: &str = r#"
#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + 999u32)]
fn t(x: u32) -> u32 { let a = 5u32; let f = |y: u32| y + a; f(x) }
"#;

// SOUNDNESS (CARDINAL): the CORRECT capture postcondition is also fail-closed in
// v1 (captures are not inlined). This pins that the capture path never verifies
// at all (fail-closed both ways) — over-rejection, never a false-verify.
const CAPTURE_CORRECT: &str = r#"
#[trust_vc::requires(x < 100u32)]
#[trust_vc::ensures(result == x + 5u32)]
fn t(x: u32) -> u32 { let a = 5u32; let f = |y: u32| y + a; f(x) }
"#;

// SOUNDNESS (CARDINAL): a divide-by-zero in the invoked body must still fail
// closed — the arith-safety path pins the body's panic-freedom independent of
// the value inline.
const DIV_ZERO: &str = r#"
#[trust_vc::requires(x == 4u32)]
#[trust_vc::ensures(result == 2u32)]
fn t(x: u32) -> u32 { let f = |a: u32, b: u32| a / b; f(x, 0u32) }
"#;

// CAPABILITY: a SAFE (non-zero divisor) invoked body still verifies — no
// over-rejection from the arith-safety pin.
const DIV_SAFE: &str = r#"
#[trust_vc::requires(x == 4u32)]
#[trust_vc::ensures(result == 2u32)]
fn t(x: u32) -> u32 { let f = |a: u32, b: u32| a / b; f(x, 2u32) }
"#;

#[test]
fn identity_closure_inline_verifies() {
    assert!(
        matches!(verify("id", ID_TRUE, "t"), VerifyResult::Verified),
        "a bare capture-free `|y| y` applied by name must inline+verify `result == x`"
    );
}

#[test]
fn addone_closure_inline_verifies() {
    assert!(
        matches!(verify("addone", ADDONE_TRUE, "t"), VerifyResult::Verified),
        "`|y| y + 1` inlined must verify `result == x + 1`"
    );
}

#[test]
fn param_used_twice_inlines_both_occurrences() {
    assert!(
        matches!(verify("twice", TWICE_TRUE, "t"), VerifyResult::Verified),
        "`|y| y + y` must substitute both occurrences and verify `result == x + x`"
    );
}

#[test]
fn false_postcondition_counterexamples() {
    let r = verify("addone_false", ADDONE_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "CARDINAL: the inline models the real body (`+1`), so `result == x` must \
         COUNTEREXAMPLE, not vacuously verify; got {r:?}"
    );
}

#[test]
fn const_body_false_postcondition_counterexamples() {
    let r = verify("const_false", CONST_FALSE, "t");
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "a constant-body closure with `result == x` (x==5) must COUNTEREXAMPLE; got {r:?}"
    );
}

#[test]
fn captured_local_wrong_postcondition_does_not_verify() {
    let r = verify("capture_wrong", CAPTURE_WRONG, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: a captured-local body is not inlined (fail-closed); a wrong \
         `result == x + 999` must NOT verify; got {r:?}"
    );
}

#[test]
fn captured_local_stays_fail_closed_both_ways() {
    let r = verify("capture_correct", CAPTURE_CORRECT, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "captures are not inlined in v1 — even the correct `result == x + 5` is \
         fail-closed (sound over-rejection), never a false-verify; got {r:?}"
    );
}

#[test]
fn divide_by_zero_in_inlined_body_fails_closed() {
    let r = verify("div_zero", DIV_ZERO, "t");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: a divide-by-zero in the invoked body must fail closed \
         (arith-safety pins the body's panic-freedom); got {r:?}"
    );
}

#[test]
fn safe_divisor_invoked_body_verifies() {
    assert!(
        matches!(verify("div_safe", DIV_SAFE, "t"), VerifyResult::Verified),
        "a safe (non-zero) invoked-body division must still verify (no over-rejection)"
    );
}
