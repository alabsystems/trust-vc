// `let _ = expr;` lowers, and DISCARDING THE VALUE DOES NOT DISCARD THE
// OBLIGATIONS (soundness guard + regression pin).
//
// Before this, `let _ = ..` hit `unsupported let pattern` in `extract_let_binding`
// and hard-errored. That is fail-closed, but it errored the WHOLE FILE: trait
// default bodies are lowered eagerly at impl-registration time, so a single
// `let _` inside one default body (`evals/verus/ported/returns_postcondition.rs`,
// `default_returns_wrong_input`) turned all 50 of that port's cases into `Error`.
//
// A wildcard discards the value but NOT the evaluation. The tempting fix — skip
// the statement — would silently drop every obligation the initializer carries
// (a callee's `requires`, an overflow check), which is the UNSOUND direction: we
// would stop checking a call merely because its result was thrown away. Instead
// `_` binds to a fresh name nothing can reference, so the initializer is lowered
// exactly as before and only the value becomes unreachable.
//
// `wildcard_let_still_discharges_callee_requires` is the load-bearing case: if it
// ever flips to Verified we are ignoring a precondition on a discarded call.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r#"
#[trust_vc::requires(x > 0u8)]
#[trust_vc::ensures(result == x)]
fn needs_positive(x: u8) -> u8 {
    x
}

// The call's `requires` is VIOLATED (0 > 0 is false). Discarding the result must
// not discard that obligation.
#[trust_vc::ensures(true)]
fn wildcard_let_violating_call() {
    let _ = needs_positive(0u8);
    trust_vc::assert!(true);
}

// Same call, precondition SATISFIED. Must verify — proves the case above fails
// for the precondition, not merely because `let _` is rejected.
#[trust_vc::ensures(true)]
fn wildcard_let_satisfying_call() {
    let _ = needs_positive(1u8);
    trust_vc::assert!(true);
}

// The discarded value must not leak a usable fact, and must not break the block.
#[trust_vc::ensures(true)]
fn wildcard_let_plain_value() {
    let _ = 5u8;
    trust_vc::assert!(true);
}

// Annotated wildcard: `let _: T = expr;`
#[trust_vc::ensures(true)]
fn wildcard_let_annotated() {
    let _: u8 = 5u8;
    trust_vc::assert!(true);
}

// Several wildcards in one block must not collide with each other.
#[trust_vc::ensures(true)]
fn wildcard_let_repeated() {
    let _ = 1u8;
    let _ = 2u8;
    let _ = 3u8;
    trust_vc::assert!(true);
}

// A wildcard must not shadow or disturb a real binding.
#[trust_vc::ensures(true)]
fn wildcard_let_does_not_clobber_real_binding(a: u8, b: u8) {
    let sum = a as int + b as int;
    let _ = a;
    trust_vc::assert!(sum == a as int + b as int);
}
"#;

fn verify(case: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_wild_let_{}_{case}.rs", std::process::id()));
    std::fs::write(&path, SRC).expect("write fixture");
    let r = verify_function_from_file(path.to_str().unwrap(), case).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    r
}

fn assert_verified(case: &str) {
    match verify(case) {
        VerifyResult::Verified => {}
        other => panic!("{case}: expected Verified, got {other:?}"),
    }
}

/// THE SOUNDNESS CASE. `let _ = needs_positive(0u8);` violates the callee's
/// `requires(x > 0)`. Throwing the result away must not throw the obligation away.
#[test]
fn wildcard_let_still_discharges_callee_requires() {
    match verify("wildcard_let_violating_call") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "UNSOUND: `let _ = needs_positive(0u8);` VERIFIED. The callee's \
             `requires(x > 0)` is violated, but discarding the result discarded the \
             precondition obligation with it."
        ),
        other => panic!("expected a counterexample on the violated precondition, got {other:?}"),
    }
}

/// Proves the case above fails for the RIGHT reason — a satisfied precondition
/// through the same `let _` shape verifies.
#[test]
fn wildcard_let_satisfying_call_verifies() {
    assert_verified("wildcard_let_satisfying_call");
}

#[test]
fn wildcard_let_shapes_lower() {
    assert_verified("wildcard_let_plain_value");
    assert_verified("wildcard_let_annotated");
    assert_verified("wildcard_let_repeated");
    assert_verified("wildcard_let_does_not_clobber_real_binding");
}
