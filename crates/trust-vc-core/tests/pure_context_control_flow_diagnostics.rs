// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for return/break/continue in PURE contexts
//! (diagnostic-parity foundation slice 2, FAMILY B).
//!
//! Upstream semantics (vir/src/modes.rs), in CHECK ORDER:
//! * ExprX::Return: (1) exec fn + ghost context — "cannot return from
//!   non-exec code in exec function"; (2) `in_forall_stmt` — "return is not
//!   allowed in 'assert ... by' statements"; (3) `in_proof_in_spec`;
//!   (4) `in_pure` — "return is not allowed in pure context".
//! * ExprX::BreakOrContinue: only (2)(3)(4), with "break/continue …" — NO
//!   exec-ghost check.
//! * ExprX::Loop in a ghost context errors FIRST with "cannot use while in
//!   proof or spec mode", before any break/continue inside it is checked.
//!
//! `in_pure` contexts include spec-fn bodies, quantifier bodies, spec-closure
//! bodies, and assert!/assume! arguments.
//!
//! Upstream test witnesses: closures.rs `return_in_closure`
//! (`proof fn p(){ let _f = |x:int| -> int { return x; }; }` — "return is not
//! allowed in pure context"). The bare spec-body `return`, the exec-fn
//! assert-arg shapes, and both 'assert ... by' strings have NO upstream test
//! (grepped rust_verify_test/tests) — they are grounded in the modes.rs
//! source checks above.
//!
//! Every rule is general (keyed on language shape + mode attribute) and
//! reject-only. Negative controls pin the legal twins: `return` in exec and
//! proof fn BODIES, closures in exec code, and break/continue in plain exec
//! loops.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

const PURE_RETURN_MSG: &str = "return is not allowed in pure context";
const PURE_BREAK_MSG: &str = "break/continue is not allowed in pure context";
const EXEC_RETURN_MSG: &str = "cannot return from non-exec code in exec function";
const ASSERT_BY_RETURN_MSG: &str = "return is not allowed in 'assert ... by' statements";
const ASSERT_BY_BREAK_MSG: &str = "break/continue is not allowed in 'assert ... by' statements";
const GHOST_LOOP_MSG: &str = "cannot use while in proof or spec mode";

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/pure_context_control_flow_diagnostics");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// The error message returned (empty string if the call did not error).
fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

// ---------------------------------------------------------------------------
// 1. "return is not allowed in pure context" — spec-fn bodies (B2, B5)
// ---------------------------------------------------------------------------

#[test]
fn spec_body_return_is_rejected_with_pure_context_message() {
    // No upstream test pins this bare shape; grounded in modes.rs
    // ExprX::Return + in_pure (push_in_pure(pure_spec_fn)). Previously a
    // SILENT ACCEPT.
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    return x;
}
"#;
    let r = verify(code, "s");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "spec-body return must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn spec_conditional_return_is_rejected_with_pure_context_message() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    if x > 0 {
        return 1;
    }
    0
}
"#;
    let r = verify(code, "s");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "spec conditional return must be rejected, got {r:?}"
    );
}

#[test]
fn spec_closure_return_is_rejected_with_pure_context_message() {
    // Spec closures are pure too (B5); the spec-body finder descends
    // closures.
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    let f = |y: u64| -> u64 { return y; };
    x
}
"#;
    let r = verify(code, "s");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "spec-closure return must be rejected, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 2. "return is not allowed in pure context" — proof-fn closures (B1)
// ---------------------------------------------------------------------------

#[test]
fn proof_closure_return_is_rejected_with_pure_context_message() {
    // Upstream closures.rs return_in_closure (verbatim shape).
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    let _f = |x: int| -> int { return x; };
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "proof-closure return must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn proof_top_level_return_stays_accepted() {
    // B3 control: `return` in a proof-fn BODY is legal upstream
    // ((Mode::Proof, _) arm of ExprX::Return).
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    return;
}
"#;
    let r = verify(code, "p");
    assert!(
        !err_message(&r).contains(PURE_RETURN_MSG),
        "top-level proof return is legal and must not fire, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "top-level proof return must keep verifying, got {r:?}"
    );
}

#[test]
fn exec_closure_return_is_not_flagged() {
    // B4 control: closures in EXEC fns are exec closures — `return` inside
    // them is legal upstream. (The shape may still hit an unrelated
    // capability error; it must not gain a pure-context rejection.)
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    let f = |x: u64| -> u64 { return x; };
    let _ = f(1);
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_RETURN_MSG) && !msg.contains(EXEC_RETURN_MSG),
        "exec-closure return must not hit the pure-context rules, got {r:?}"
    );
}

#[test]
fn exec_body_return_is_not_flagged() {
    let code = r#"
#[trust_vc::ensures(result == 5)]
fn e() -> u64 {
    return 5;
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_RETURN_MSG) && !msg.contains(EXEC_RETURN_MSG),
        "exec-body return is legal and must not fire the new rules, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. assert!/assume! arguments are pure contexts (B6, B6b, B7, B10)
// ---------------------------------------------------------------------------

#[test]
fn proof_return_in_assert_arg_is_rejected_with_pure_context_message() {
    // B6: assert args are in_pure; proof fns pass the exec-ghost check.
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert!({ if false { return; } true });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "proof assert-arg return must be rejected with the pure-context message, got {r:?}"
    );
}

#[test]
fn exec_return_in_assert_arg_gets_non_exec_message() {
    // B6b: upstream check (1) — exec fn + ghost context — PRECEDES the
    // pure-context checks, so the exec message wins.
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    trust_vc::assert!({ if false { return; } true });
}
"#;
    let r = verify(code, "e");
    assert!(
        err_message(&r).contains(EXEC_RETURN_MSG),
        "exec assert-arg return must get the non-exec-return message, got {r:?}"
    );
}

#[test]
fn exec_break_in_assert_arg_is_rejected_with_pure_context_message() {
    // B7: the loop is OUTSIDE the assert (legal exec loop); the `break`
    // inside the ghost argument is rejected — upstream BreakOrContinue has
    // NO exec-ghost check, so the pure-context message is mode-independent.
    let code = r#"
#[trust_vc::ensures(true)]
fn e(n: u64) {
    let mut n = n;
    while n > 0 {
        trust_vc::assert!({ if n == 1 { break; } true });
        n = n - 1;
    }
}
"#;
    let r = verify(code, "e");
    assert!(
        err_message(&r).contains(PURE_BREAK_MSG),
        "break inside an assert argument must be rejected, got {r:?}"
    );
}

#[test]
fn proof_return_in_quantifier_body_is_rejected() {
    // B10: quantifier bodies are pure; previously errored with an internal
    // fail-closed encoder message ("assertion operand must encode to a Bool
    // term") — now carries the upstream message.
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert!(forall(|x: u64| { return true; }));
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "return in a quantifier body must be rejected with the pure-context message, got {r:?}"
    );
}

#[test]
fn assume_arg_return_is_rejected_mode_keyed() {
    let proof_code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assume!({ if false { return; } true });
}
"#;
    let r = verify(proof_code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "proof assume-arg return must be rejected with the pure-context message, got {r:?}"
    );

    let exec_code = r#"
#[trust_vc::ensures(true)]
fn e() {
    trust_vc::assume!({ if false { return; } true });
}
"#;
    let r = verify(exec_code, "e");
    assert!(
        err_message(&r).contains(EXEC_RETURN_MSG),
        "exec assume-arg return must get the non-exec-return message, got {r:?}"
    );
}

#[test]
fn loop_inside_assert_arg_gets_ghost_loop_message() {
    // Upstream order witness: a loop in a ghost context is rejected with
    // "cannot use while in proof or spec mode" BEFORE any break/continue
    // inside it is checked — the walker is pre-order to match.
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    trust_vc::assert!({ loop { break; } true });
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        msg.contains(GHOST_LOOP_MSG),
        "loop inside an assert argument must get the ghost-loop message, got {r:?}"
    );
    assert!(
        !msg.contains(PURE_BREAK_MSG),
        "the enclosed break must NOT win over the enclosing-loop message, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 4. `assert forall … by` proof blocks (B12; source-grounded, no upstream test)
// ---------------------------------------------------------------------------

#[test]
fn assert_forall_by_proof_block_return_is_rejected() {
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert_forall_by!(|x: int| x + 0 == x, { return; });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(ASSERT_BY_RETURN_MSG),
        "return in an assert-forall-by proof block must be rejected, got {r:?}"
    );
}

#[test]
fn assert_forall_by_proof_block_break_is_rejected() {
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert_forall_by!(|x: int| x + 0 == x, { if x == 0 { break; } });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(ASSERT_BY_BREAK_MSG),
        "break in an assert-forall-by proof block must be rejected, got {r:?}"
    );
}

#[test]
fn legit_assert_forall_by_stays_accepted() {
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert_forall_by!(|x: int| x + 0 == x, {});
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    assert!(
        !msg.contains(ASSERT_BY_RETURN_MSG)
            && !msg.contains(ASSERT_BY_BREAK_MSG)
            && !msg.contains(GHOST_LOOP_MSG),
        "control-flow-free assert-forall-by must not fire any new rule, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "legit assert-forall-by must keep verifying, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 5. Remaining negative controls: legal exec shapes stay legal (B8 + asserts)
// ---------------------------------------------------------------------------

#[test]
fn exec_loop_break_stays_accepted() {
    // B8 control: break/continue in a plain exec loop is legal.
    let code = r#"
#[trust_vc::ensures(true)]
fn e(n: u64) {
    let mut n = n;
    while n > 0 {
        if n == 1 {
            break;
        }
        n = n - 1;
    }
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_BREAK_MSG) && !msg.contains(GHOST_LOOP_MSG),
        "plain exec loop with break must not fire the new rules, got {r:?}"
    );
}

#[test]
fn plain_assert_stays_verified() {
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    let x = 1u64;
    trust_vc::assert!(x == 1);
}
"#;
    let r = verify(code, "e");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "control-flow-free assert must keep verifying, got {r:?}"
    );
}

#[test]
fn spec_body_without_return_is_unaffected() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64, y: u64) -> bool {
    x <= y
}
"#;
    let r = verify(code, "s");
    assert!(
        !err_message(&r).contains(PURE_RETURN_MSG),
        "return-free spec body must not fire the pure-context return rule, got {r:?}"
    );
}

// ── corners fixed after the adversarial verify ───────────────────────────────

/// The assert-forall-by CONDITION position is `in_forall_stmt` upstream (the
/// flag covers the whole statement and precedes `in_pure`, modes.rs :3123),
/// so a return there gets the 'assert ... by' message, not the pure-context
/// one.
#[test]
fn assert_forall_by_condition_return_gets_assert_by_message() {
    let code = r#"
#[trust_vc::proof]
fn p() {
    trust_vc::assert_forall_by!(|x: u64| { if x > 0 { return true; } true }, { trust_vc::assert!(true); });
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    assert!(
        msg.contains("return is not allowed in 'assert ... by' statements"),
        "condition-position return must get the in_forall_stmt message, got {r:?}"
    );
}

/// Nested returns-tuple binding idents collide too — upstream
/// check_return_idents walks nested patterns.
#[test]
fn nested_tuple_returns_binding_collision_detected() {
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns((r, (b, c)))]
fn f(b: u64) -> (u64, (u64, u64)) {
    (0, (b, 1))
}
"#;
    let r = verify(code, "f");
    let msg = err_message(&r);
    assert!(
        msg.contains("return value name collides with a parameter name"),
        "nested tuple binding collision must be detected, got {r:?}"
    );
}
