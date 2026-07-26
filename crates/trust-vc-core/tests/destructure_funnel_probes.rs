// Adversarial funnel probes (temporary — Verify step). Does the
// destructuring-assignment reject cover every walk path (loop bodies,
// branches), i.e. is the old silent-drop unsoundness fully closed?

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/zz_adversarial_funnel_probes");
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

// Destructuring assignment inside an if-else branch followed by an assert on
// the stale value: must NOT be Verified (either the destructuring reject or
// another fail-closed error is acceptable; silent Verified is the bug).
#[test]
fn funnel_destructure_in_else_branch_must_not_verify_stale() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test(flag: bool) {
    let mut a = 0u64;
    let mut b = 0u64;
    if flag {
        a = 7;
    } else {
        (a, b) = (1, 2);
    }
    trust_vc::assert!(a == 0 || a == 7);
}
"#;
    let r = verify(code, "test");
    println!("else-branch destructure => {r:?}");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "else-branch destructuring must not silently verify stale values, got {r:?}"
    );
}

// Destructuring assignment inside a while-loop body with an invariant-free
// loop: must NOT be Verified.
#[test]
fn funnel_destructure_in_loop_body_must_not_verify_stale() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let mut a = 0u64;
    let mut b = 0u64;
    let mut i = 0u64;
    while i < 1 {
        (a, b) = (1, 2);
        i = i + 1;
    }
    trust_vc::assert!(a == 0);
}
"#;
    let r = verify(code, "test");
    println!("loop-body destructure => {r:?}");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "loop-body destructuring must not silently verify stale values, got {r:?}"
    );
}

// Statement-position destructure with NO later use — still must reject (the
// upstream error is unconditional on the feature).
#[test]
fn funnel_bare_statement_destructure_rejected() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let mut x = 0u64;
    let mut y = 0u64;
    (x, y) = (9, 9);
}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r).contains("destructuring assignment"),
        "bare-statement destructure must be rejected, got {r:?}"
    );
}
