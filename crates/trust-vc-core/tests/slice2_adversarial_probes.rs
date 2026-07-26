// Adversarial verification probes (verifier-authored, to be deleted).
use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

const COLLISION_MSG: &str = "return value name collides with a parameter name";
const PURE_RETURN_MSG: &str = "return is not allowed in pure context";
const PURE_BREAK_MSG: &str = "break/continue is not allowed in pure context";
const EXEC_RETURN_MSG: &str = "cannot return from non-exec code in exec function";
const ASSERT_BY_RETURN_MSG: &str = "return is not allowed in 'assert ... by' statements";
const ASSERT_BY_BREAK_MSG: &str = "break/continue is not allowed in 'assert ... by' statements";
const GHOST_LOOP_MSG: &str = "cannot use while in proof or spec mode";

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/zz_adversarial_probes");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

// ============ FAMILY A GENERALITY (novel instances) ============

#[test]
fn a_g1_mut_param_collision() {
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns(n)]
fn f(mut n: u32) -> u32 { n = n + 0; n }
"#;
    let r = verify(code, "f");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "mut-param collision must fire, got {r:?}"
    );
}

#[test]
fn a_g2_contract_nested_pattern_param_collision() {
    let code = r#"
#[trust_vc::contract(ensures(true), returns(b))]
fn g((a, b): (u32, u32)) -> u32 { a }
"#;
    let r = verify(code, "g");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "contract-form nested-pattern collision must fire, got {r:?}"
    );
}

#[test]
fn a_g3_nested_tuple_returns_collision_probe() {
    // Upstream check_return_idents walks nested return patterns: `((r, (b, c)):
    // ...)` collides on param b. Does the impl's TOP-LEVEL-only filter_map see it?
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns((r, (b, c)))]
fn h(b: u32) -> (u32, (u32, u32)) { (1, (2, 3)) }
"#;
    let r = verify(code, "h");
    let msg = err_message(&r);
    eprintln!("A-G3 nested-tuple collision probe result: {msg:?}");
    // Not asserted PASS/FAIL — recorded for the report.
}

// ============ FAMILY A OVER-REJECTION ============

#[test]
fn a_o1_local_var_shadow_not_flagged() {
    let code = r#"
#[trust_vc::ensures(r == 1)]
#[trust_vc::returns(r)]
fn f() -> u64 { let r = 1u64; r }
"#;
    let r = verify(code, "f");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "binding colliding with a LOCAL (not a param) must not fire, got {r:?}"
    );
}

#[test]
fn a_o2_non_colliding_binding_verifies() {
    let code = r#"
#[trust_vc::ensures(m == n)]
#[trust_vc::returns(m)]
fn f(n: u64) -> u64 { n }
"#;
    let r = verify(code, "f");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "non-colliding binding must verify, got {r:?}"
    );
}

#[test]
fn a_o3_shadowy_name_not_flagged() {
    let code = r#"
#[trust_vc::ensures(x2 == x)]
#[trust_vc::returns(x2)]
fn f(x: u64) -> u64 { x }
"#;
    let r = verify(code, "f");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "shadow-y but distinct name must not fire, got {r:?}"
    );
    assert!(matches!(r, Ok(VerifyResult::Verified)), "got {r:?}");
}

#[test]
fn a_o4_nested_pattern_param_non_colliding() {
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns(c)]
fn g((a, b): (u32, u32)) -> u32 { a + b }
"#;
    let r = verify(code, "g");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "non-colliding binding with nested-pattern params must not fire, got {r:?}"
    );
}

#[test]
fn a_o5_explicit_result_binding_not_flagged() {
    let code = r#"
#[trust_vc::ensures(result == k)]
#[trust_vc::returns(result)]
fn f(k: u64) -> u64 { k }
"#;
    let r = verify(code, "f");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "explicit `result` binding with no `result` param must not fire, got {r:?}"
    );
    assert!(matches!(r, Ok(VerifyResult::Verified)), "got {r:?}");
}

// ============ FAMILY B GENERALITY (novel instances) ============

#[test]
fn b_g1_spec_match_arm_return() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    match x {
        0 => return 1,
        _ => 0,
    }
}
"#;
    let r = verify(code, "s");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "spec match-arm return must fire, got {r:?}"
    );
}

#[test]
fn b_g2_spec_nested_closure_return() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    let f = |y: u64| { let g = |z: u64| -> u64 { return z; }; y };
    x
}
"#;
    let r = verify(code, "s");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "spec nested-closure return must fire, got {r:?}"
    );
}

#[test]
fn b_g3_proof_closure_in_if_return() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p(c: bool) {
    if c {
        let _f = |x: u64| -> u64 { return x; };
    }
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "proof closure-in-if return must fire, got {r:?}"
    );
}

#[test]
fn b_g4_proof_nested_closure_return() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    let _f = |x: u64| { let g = |y: u64| -> u64 { return y; }; x };
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "proof nested-closure return must fire, got {r:?}"
    );
}

#[test]
fn b_g5_proof_continue_in_assume_arg() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p(n: u64) {
    trust_vc::assume!({ if n == 0 { continue; } true });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_BREAK_MSG),
        "continue in assume! arg must fire the break/continue message, got {r:?}"
    );
}

#[test]
fn b_g6_proof_closure_return_inside_assert_arg() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert!({ let f = |x: u64| -> u64 { return x; }; true });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(PURE_RETURN_MSG),
        "closure return inside assert! arg must fire, got {r:?}"
    );
}

#[test]
fn b_g7_assert_forall_by_continue_in_proof_block() {
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert_forall_by!(|x: int| x + 0 == x, { if x == 0 { continue; } });
}
"#;
    let r = verify(code, "p");
    assert!(
        err_message(&r).contains(ASSERT_BY_BREAK_MSG),
        "continue in assert-forall-by proof block must fire, got {r:?}"
    );
}

#[test]
fn b_g8_assert_forall_by_condition_return_message_probe() {
    // Upstream typing0 in the assert-by CONDITION has BOTH in_forall_stmt and
    // in_pure set, and modes.rs checks in_forall_stmt (3120) BEFORE in_pure
    // (3130) — so upstream emits the 'assert ... by' message here, not the
    // pure-context one.
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert_forall_by!(|x: int| { return true; }, {});
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    eprintln!("B-G8 condition-return message: {msg:?}");
    eprintln!(
        "B-G8 pure={} assert_by={}",
        msg.contains(PURE_RETURN_MSG),
        msg.contains(ASSERT_BY_RETURN_MSG)
    );
}

#[test]
fn b_g9_for_loop_in_assert_arg() {
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    trust_vc::assert!({ for _i in 0..1 { } true });
}
"#;
    let r = verify(code, "e");
    assert!(
        err_message(&r).contains(GHOST_LOOP_MSG),
        "for-loop in assert arg must get the ghost-loop message, got {r:?}"
    );
}

// ============ FAMILY B OVER-REJECTION ============

#[test]
fn b_o1_labeled_nested_loop_break_exec() {
    let code = r#"
#[trust_vc::ensures(true)]
fn e(n: u64) {
    let mut n = n;
    'outer: while n > 0 {
        let mut m = n;
        while m > 0 {
            if m == 1 { break 'outer; }
            m = m - 1;
        }
        n = n - 1;
    }
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_BREAK_MSG)
            && !msg.contains(GHOST_LOOP_MSG)
            && !msg.contains(PURE_RETURN_MSG)
            && !msg.contains(EXEC_RETURN_MSG),
        "labeled nested exec loops must not fire any new rule, got {r:?}"
    );
}

#[test]
fn b_o2_continue_in_nested_exec_loop() {
    let code = r#"
#[trust_vc::ensures(true)]
fn e(n: u64) {
    let mut n = n;
    while n > 0 {
        n = n - 1;
        if n == 2 { continue; }
    }
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_BREAK_MSG) && !msg.contains(GHOST_LOOP_MSG),
        "continue in an exec loop must not fire, got {r:?}"
    );
}

#[test]
fn b_o3_proof_conditional_top_level_return() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p(c: bool) {
    if c { return; }
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_RETURN_MSG) && !msg.contains(EXEC_RETURN_MSG),
        "conditional top-level return in a proof fn is legal, got {r:?}"
    );
}

#[test]
fn b_o4_exec_closure_with_own_loop_break() {
    let code = r#"
#[trust_vc::ensures(true)]
fn e() {
    let f = |n: u64| -> u64 {
        let mut n = n;
        while n > 1 { n = n - 1; if n == 2 { break; } }
        n
    };
    let _ = f(5);
}
"#;
    let r = verify(code, "e");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_BREAK_MSG)
            && !msg.contains(GHOST_LOOP_MSG)
            && !msg.contains(PURE_RETURN_MSG),
        "exec closure with its own loop+break must not fire, got {r:?}"
    );
}

#[test]
fn b_o5_proof_body_while_loop_not_ghost_loop_flagged() {
    // Deferred slice: full-body proof-fn loops stay accepted (capability).
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    let mut i = 0u64;
    while i < 1 { i = i + 1; }
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    assert!(
        !msg.contains(GHOST_LOOP_MSG) && !msg.contains(PURE_BREAK_MSG),
        "proof-body loop must not be newly rejected (deferred slice), got {r:?}"
    );
}

#[test]
fn b_o6_proof_assert_forall_no_control_flow() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn p() {
    trust_vc::assert!(forall(|x: u64| x == x));
}
"#;
    let r = verify(code, "p");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_RETURN_MSG)
            && !msg.contains(PURE_BREAK_MSG)
            && !msg.contains(GHOST_LOOP_MSG),
        "control-flow-free quantifier assert must not fire, got {r:?}"
    );
}

#[test]
fn b_o7_nested_fn_item_return_in_spec() {
    // A nested fn item has its own (exec) mode; return inside it is legal.
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn s(x: u64) -> u64 {
    fn inner() -> u64 { return 5; }
    x
}
"#;
    let r = verify(code, "s");
    let msg = err_message(&r);
    assert!(
        !msg.contains(PURE_RETURN_MSG),
        "return inside a nested fn item must not fire the spec-body rule, got {r:?}"
    );
}
