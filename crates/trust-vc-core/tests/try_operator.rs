// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The `?` (Try) operator on Option/Result-returning functions, desugared to an
//! equivalent tail `match` (`let v = g()?; REST` -> `match g() { Some(v) => REST,
//! None => None }`). Behavior-preserving, so the extractor checks the
//! postcondition on BOTH the success and the failure (early-return) arm.
//!
//! CARDINAL: a postcondition that is false on the None/Err short-circuit path
//! must be REFUTED (the `?` early-return is not silently dropped).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        let mut p = std::env::temp_dir();
        p.push(format!("tvc_try_{}_{}.rs", std::process::id(), id));
        std::fs::write(&p, src).expect("write fixture");
        let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
        let _ = std::fs::remove_file(&p);
        r
    })
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
fn g(x: u64) -> Option<u64> { Some(x) }
fn h(x: u64) -> Result<u64, u64> { Ok(x) }

// Basic ? on Option / Result.
#[trust_vc::ensures(true)]
fn opt_basic(x: u64) -> Option<u64> { let v = g(x)?; Some(v) }
#[trust_vc::ensures(true)]
fn res_basic(x: u64) -> Result<u64, u64> { let v = h(x)?; Ok(v) }

// Sound postcondition tying result to the input's variant.
#[trust_vc::ensures(result.is_some() == o.is_some())]
fn opt_variant(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }

// On the SUCCESS path the bound value equals the input's payload (no arithmetic,
// so no overflow obligation clouds the check).
#[trust_vc::ensures(o == Some(5u64) ==> result == Some(5u64))]
fn opt_success_value(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }

// Multiple ? in sequence (both early-return paths must be checked).
#[trust_vc::ensures((a.is_some() && b.is_some()) == result.is_some())]
fn opt_multi(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    let x = a?;
    let _y = b?;
    Some(x)
}

// A typed binding is part of the source semantics. The desugar must not erase
// it and then verify a body under the operand's different payload type.
#[trust_vc::ensures(true)]
fn opt_typed_mismatch(o: Option<u64>) -> Option<u64> {
    let v: bool = o?;
    Some(v as u64)
}

// CARDINAL LIAR #1: result.is_some() is FALSE when o is None (early return).
#[trust_vc::ensures(result.is_some())]
fn opt_liar_isnone(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }

// CARDINAL LIAR #2: false on the SUCCESS path (v could be anything).
#[trust_vc::ensures(result == Some(0u64))]
fn opt_liar_success(o: Option<u64>) -> Option<u64> { let v = o?; Some(v) }

// CARDINAL LIAR #3: Result — Ok on failure path is false.
#[trust_vc::ensures(result.is_ok())]
fn res_liar(r: Result<u64, u64>) -> Result<u64, u64> { let v = r?; Ok(v) }

// ---- ? in the TAIL expression (Some(g()?)) ----
fn pick(x: u64, y: u64) -> u64 { x }
#[trust_vc::ensures(result.is_some() == o.is_some())]
fn tail_some_wrap(o: Option<u64>) -> Option<u64> { Some(o?) }
// Two ? in the tail: result is Some iff BOTH succeed.
#[trust_vc::ensures((a.is_some() && b.is_some()) == result.is_some())]
fn tail_two_try(a: Option<u64>, b: Option<u64>) -> Option<u64> { Some(pick(a?, b?)) }
// CARDINAL: false on the None short-circuit of a tail ?.
#[trust_vc::ensures(result.is_some())]
fn tail_some_wrap_liar(o: Option<u64>) -> Option<u64> { Some(o?) }
// A ? nested in a CONDITIONAL stays fail-closed (unconditional-rewrite would be
// wrong), so this false claim must NOT verify.
#[trust_vc::ensures(result.is_some())]
fn tail_conditional_try(c: bool, o: Option<u64>) -> Option<u64> {
    if c { Some(o?) } else { None }
}

// CARDINAL: a generated tail-? binder must never capture a user binding.
// With a hard-coded `__trust_vc_try_0`, the rewrite changes the tuple's second
// field from the parameter to the Option payload and makes this liar provable.
#[trust_vc::ensures(
    (o == Some(1u64) && __trust_vc_try_0 == 2u64) ==>
        result == Some(1u64)
)]
fn tail_try_generated_name_collision(
    o: Option<u64>,
    __trust_vc_try_0: u64,
) -> Option<u64> {
    Some((o?, __trust_vc_try_0).1)
}

// CARDINAL: Rust evaluates tuple elements left-to-right, so the division
// panics before the later `o?` observes None. Hoisting that `?` around the
// entire tail expression would skip a real panic obligation and verify this.
#[trust_vc::requires(o.is_none() && d == 0u64)]
#[trust_vc::ensures(true)]
fn tail_try_must_not_hoist_past_division(o: Option<u64>, d: u64) -> Option<u64> {
    Some((1u64 / d, o?).1)
}

// CARDINAL: evaluating a value path as an earlier call argument can move or
// reborrow it. Hoisting the later `?` would turn this compiler-invalid aliasing
// order into a valid call and let an invalid source function verify.
fn take_mut(_: &mut u64, _: u64) -> u64 { 0u64 }
fn get_mut(x: &mut u64) -> Option<u64> { Some(*x) }
#[trust_vc::ensures(true)]
fn tail_try_must_not_hoist_past_mut_reborrow(x: &mut u64) -> Option<u64> {
    Some(take_mut(x, get_mut(x)?))
}

// A plain `let` requires an irrefutable pattern. Desugaring a refutable pattern
// into a partial match must not turn an invalid source function into Verified.
#[trust_vc::ensures(true)]
fn try_refutable_let_pattern(o: Option<Option<u64>>) -> Option<u64> {
    let Some(v) = o?;
    Some(v)
}

// Statement attributes are part of source semantics (`cfg` can remove the
// whole call). Until attributes are interpreted exactly, the rewrite must keep
// attributed bindings on the existing fail-closed Expr::Try path.
#[trust_vc::ensures(true)]
fn try_attributed_binding(o: Option<u64>) -> Option<u64> {
    #[allow(unused_variables)]
    let v = o?;
    Some(v)
}
"#;

#[test]
fn try_operator_positives() {
    for f in [
        "opt_basic",
        "res_basic",
        "opt_variant",
        "opt_success_value",
        "opt_multi",
        "tail_some_wrap",
        "tail_two_try",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify (sound ? desugar); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn try_operator_cardinal_liars() {
    for f in [
        "opt_liar_isnone",
        "opt_liar_success",
        "res_liar",
        "tail_some_wrap_liar",
        "tail_conditional_try",
        "tail_try_generated_name_collision",
        "tail_try_must_not_hoist_past_division",
        "tail_try_must_not_hoist_past_mut_reborrow",
    ] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}` must NOT verify (postcondition false on a ? path)"
        );
    }
}

#[test]
fn try_operator_unsupported_binding_shapes_fail_closed() {
    for f in ["try_refutable_let_pattern", "try_attributed_binding"] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "`{f}` must remain fail closed rather than change source semantics"
        );
    }
}

#[test]
fn try_operator_typed_binding_mismatch_fails_closed() {
    assert!(
        !verified(&verify("opt_typed_mismatch", "opt_typed_mismatch", SRC)),
        "a typed `?` binding must not verify after erasing its source annotation"
    );
}

#[test]
fn try_operator_requires_authoritative_builtin_type_provenance() {
    const CUSTOM_OPTION: &str = r#"
enum Option<T> { Some(T), None }
#[trust_vc::ensures(true)]
fn custom_option(o: Option<u64>) -> Option<u64> {
    let v = o?;
    Option::Some(v)
}
"#;
    assert!(
        !verified(&verify("custom_option", "custom_option", CUSTOM_OPTION)),
        "a source-defined `Option` must not receive built-in Try semantics"
    );

    const TRAILING_OPTION: &str = r#"
mod user { pub enum Option<T> { Some(T), None } }
#[trust_vc::ensures(true)]
fn trailing_option(o: user::Option<u64>) -> user::Option<u64> {
    let v = o?;
    user::Option::Some(v)
}
"#;
    assert!(
        !verified(&verify(
            "trailing_option",
            "trailing_option",
            TRAILING_OPTION,
        )),
        "a trailing `Option` path segment is not authoritative provenance"
    );
}

#[test]
fn result_try_requires_identity_error_conversion_and_matching_family() {
    const RESULT_MISMATCHES: &str = r#"
#[trust_vc::ensures(true)]
fn differing_error(r: Result<u64, u32>) -> Result<u64, u64> {
    let v = r?;
    Ok(v)
}

#[trust_vc::ensures(true)]
fn differing_family(r: Result<u64, u64>) -> Option<u64> {
    let v = r?;
    Some(v)
}
"#;
    for function in ["differing_error", "differing_family"] {
        assert!(
            !verified(&verify(function, function, RESULT_MISMATCHES)),
            "`{function}` must stay fail closed without exact residual authority"
        );
    }
}

#[test]
fn imported_some_none_do_not_capture_generated_constructors() {
    const CAPTURE: &str = r#"
enum Capture<T> { Some(T), None }
use Capture::{Some, None};

#[trust_vc::ensures(result.is_some() == o.is_some())]
fn constructor_capture(
    o: std::option::Option<u64>,
) -> std::option::Option<u64> {
    let v = o?;
    std::option::Option::Some(v)
}
"#;
    assert!(
        verified(&verify(
            "constructor_capture",
            "constructor_capture",
            CAPTURE
        )),
        "generated Try constructors must be canonically qualified"
    );
}

#[test]
fn operand_provenance_rejects_shadowed_parameters_and_unresolved_helpers() {
    const OPERAND_PROVENANCE: &str = r#"
enum UserOption<T> { Some(T), None }

#[trust_vc::ensures(true)]
fn shadowed_parameter(o: Option<u64>) -> Option<u64> {
    let o = UserOption::Some(1u64);
    let v = o?;
    Some(v)
}

mod nested {
    pub fn hidden_g(x: u64) -> Option<u64> { Some(x) }
}
#[trust_vc::ensures(true)]
fn wrong_module(x: u64) -> Option<u64> {
    let v = hidden_g(x)?;
    Some(v)
}

fn exact_g(x: u64) -> Option<u64> { Some(x) }
#[trust_vc::ensures(true)]
fn wrong_argument_type(b: bool) -> Option<u64> {
    let v = exact_g(b)?;
    Some(v)
}
"#;
    for function in ["shadowed_parameter", "wrong_module", "wrong_argument_type"] {
        assert!(
            !verified(&verify(function, function, OPERAND_PROVENANCE)),
            "`{function}` must stay fail closed without an exact operand type proof"
        );
    }
}
