// Adversarial verification probes (temporary — written by the Verify step,
// not part of the change under review). Novel instances of each rule shape
// (different names/nesting/types) + boundary legit-code probes.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/zz_adversarial_verify_probes");
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

// ---- Rule 1 generality: novel spec-body assignment shapes -----------------

#[test]
fn novel1a_spec_assignment_in_nested_block() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn accumulate(seed: i32) -> i32 {
    let mut acc: i32 = seed;
    {
        acc = 3;
    }
    acc
}
"#;
    let r = verify(code, "accumulate");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "nested-block spec assignment must fire, got {r:?}"
    );
}

#[test]
fn novel1b_spec_compound_assignment_inside_closure() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn tally(base: u32) -> u32 {
    let bump = |k: u32| {
        let mut t = k;
        t <<= 1;
        t
    };
    bump(base)
}
"#;
    let r = verify(code, "tally");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "closure-body spec compound assignment must fire, got {r:?}"
    );
}

// ---- Rule 2 generality: novel proof non-mut-param assignments -------------

#[test]
fn novel2a_proof_param_assignment_in_nested_block() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn adjust(counter: i64) {
    {
        counter = 9;
    }
}
"#;
    let r = verify(code, "adjust");
    assert!(
        err_message(&r).contains("variable `counter` is not marked mutable"),
        "nested-block proof param assignment must fire with interpolated name, got {r:?}"
    );
}

#[test]
fn novel2b_proof_param_shl_assign_in_if() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn scale(width: u32) {
    if true {
        width <<= 1;
    }
}
"#;
    let r = verify(code, "scale");
    assert!(
        err_message(&r).contains("variable `width` is not marked mutable"),
        "if-nested proof param shl-assign must fire, got {r:?}"
    );
}

// ---- Rule 3 generality: novel spec mut-param signatures --------------------

#[test]
fn novel3a_spec_mut_bool_param() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn pick(mut flag: bool) -> bool {
    flag
}
"#;
    let r = verify(code, "pick");
    assert!(
        err_message(&r).contains("mut argument not allowed for spec functions"),
        "spec mut bool param must fire, got {r:?}"
    );
}

#[test]
fn novel3b_spec_second_param_mut() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn mix(a: i64, mut b: i64) -> i64 {
    a + b
}
"#;
    let r = verify(code, "mix");
    assert!(
        err_message(&r).contains("mut argument not allowed for spec functions"),
        "spec second-position mut param must fire, got {r:?}"
    );
}

// ---- Rule 4 generality: novel mut-self receivers ---------------------------

#[test]
fn novel4a_mut_self_different_names() {
    let code = r#"
struct Gadget {
    n: u64,
}

impl Gadget {
    #[trust_vc::ensures(true)]
    fn consume(mut self) {
        self.n = 1;
    }
}
"#;
    let r = verify(code, "consume");
    assert!(
        err_message(&r)
            .contains("The verifier does not yet support the following Rust feature: mut self"),
        "novel mut-self method must fire, got {r:?}"
    );
}

#[test]
fn novel4b_mut_self_with_extra_params_proof_mode() {
    let code = r#"
struct Ledger {
    total: u64,
}

impl Ledger {
    #[trust_vc::proof]
    #[trust_vc::ensures(true)]
    fn merge(mut self, other: u64) {
        let _ = other;
    }
}
"#;
    let r = verify(code, "merge");
    assert!(
        err_message(&r)
            .contains("The verifier does not yet support the following Rust feature: mut self"),
        "proof-mode mut-self with extra params must fire, got {r:?}"
    );
}

// ---- Rule 5 generality: novel destructuring-assignment LHS shapes ----------

#[test]
fn novel5a_paren_wrapped_tuple_destructuring_assignment() {
    let code = r#"
#[trust_vc::ensures(true)]
fn swapper() {
    let mut p = 0u64;
    let mut q = 0u64;
    ((p, q)) = (3u64, 4u64);
    let _ = (p, q);
}
"#;
    let r = verify(code, "swapper");
    assert!(
        err_message(&r).contains(
            "The verifier does not yet support the following Rust feature: destructuring assignment"
        ),
        "paren-wrapped tuple destructuring assignment must fire, got {r:?}"
    );
}

#[test]
fn novel5b_struct_destructuring_assignment_in_if() {
    let code = r#"
struct Pt {
    x: u64,
    y: u64,
}

#[trust_vc::ensures(true)]
fn splat(p: Pt) {
    let mut a = 0u64;
    let mut b = 0u64;
    if true {
        Pt { x: a, y: b } = p;
    }
    let _ = (a, b);
}
"#;
    let r = verify(code, "splat");
    assert!(
        err_message(&r).contains(
            "The verifier does not yet support the following Rust feature: destructuring assignment"
        ),
        "struct-pattern destructuring assignment must fire, got {r:?}"
    );
}

// ---- Boundary legit-code probes (must NOT reject) ---------------------------

#[test]
fn legit_exec_mut_param_assigned_in_loop() {
    let code = r#"
#[trust_vc::ensures(true)]
fn spin(mut i: u64) {
    while i < 3 {
        i += 1;
    }
}
"#;
    let r = verify(code, "spin");
    let msg = err_message(&r);
    assert!(
        !msg.contains("pure context") && !msg.contains("not marked mutable"),
        "exec loop assignment must not hit the new rules, got {r:?}"
    );
}

#[test]
fn legit_ref_mut_self_exec_method_with_field_assign() {
    let code = r#"
struct Counter {
    v: u64,
}

impl Counter {
    #[trust_vc::ensures(self.v == old(self).v + 1)]
    fn tick(&mut self) {
        self.v = self.v + 1;
    }
}
"#;
    let r = verify(code, "tick");
    let msg = err_message(&r);
    assert!(
        !msg.contains("mut self") && !msg.contains("pure context"),
        "&mut self exec method must not hit the new rules, got {r:?}"
    );
}

#[test]
fn legit_exec_local_assignment_in_loop() {
    let code = r#"
#[trust_vc::ensures(true)]
fn count() {
    let mut i: u64 = 0;
    while i < 4 {
        i = i + 1;
    }
}
"#;
    let r = verify(code, "count");
    let msg = err_message(&r);
    assert!(
        !msg.contains("pure context") && !msg.contains("not marked mutable"),
        "exec loop-local assignment must not hit the new rules, got {r:?}"
    );
}

#[test]
fn legit_spec_fn_returning_tuple() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn pair(x: u64, y: u64) -> (u64, u64) {
    (x, y)
}
"#;
    let r = verify(code, "pair");
    let msg = err_message(&r);
    assert!(
        !msg.contains("pure context") && !msg.contains("destructuring assignment"),
        "spec fn returning a tuple must not hit the new rules, got {r:?}"
    );
}

#[test]
fn legit_let_destructure_chain() {
    let code = r#"
#[trust_vc::ensures(true)]
fn chain() {
    let (a, b) = (1u64, 2u64);
    let (c, d) = (b, a);
    trust_vc::assert!(c == 2);
    trust_vc::assert!(d == 1);
}
"#;
    let r = verify(code, "chain");
    let msg = err_message(&r);
    assert!(
        !msg.contains("destructuring assignment"),
        "let-destructure chain must not hit the destructuring rule, got {r:?}"
    );
    // NOTE: base main cannot lower a CHAINED let-destructure today (the
    // second tuple RHS fails "unresolved variable `b`" — a PRE-EXISTING
    // lowering gap proven via stash on clean aa97668, independent of the
    // diagnostics). This test pins only that the destructuring-assignment
    // rule does not misfire; the chain-lowering gap is tracked separately.
    // A simple (non-chained) let-destructure staying Verified is pinned by
    // funnel_* and the mode_spec_context_diagnostics controls.
}

#[test]
fn legit_spec_fn_with_nested_exec_item_containing_assignment() {
    // Nested item has its own mode: the spec pure-context rule must not fire
    // on an assignment inside a nested exec fn item.
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn outer(x: u64) -> u64 {
    fn helper() -> u64 {
        let mut t = 0u64;
        t = 1;
        t
    }
    x
}
"#;
    let r = verify(code, "outer");
    let msg = err_message(&r);
    assert!(
        !msg.contains("pure context"),
        "nested exec item assignment must not fire the spec pure-context rule, got {r:?}"
    );
}

// ---- Corner probes the implementer's notes did / did not cover -------------

// Param rebound by `if let Some(mut o) = o` — the rebound binding IS mut, so
// upstream would NOT reject the assignment. Does rule 2 falsely fire?
#[test]
fn corner_if_let_mut_rebind_of_param() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn peel(o: Option<u64>) {
    if let Some(mut o) = o {
        o = 5;
        let _ = o;
    }
}
"#;
    let r = verify(code, "peel");
    let msg = err_message(&r);
    println!("corner_if_let_mut_rebind_of_param => {r:?}");
    assert!(
        !msg.contains("not marked mutable"),
        "if-let mut-rebound param assignment falsely fires rule 2 (upstream accepts): {r:?}"
    );
}

// Same via match arm (tracked by visit_arm) — should be shadow-safe.
#[test]
fn corner_match_arm_mut_rebind_of_param() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn peel2(o: Option<u64>) {
    match o {
        Some(mut o) => {
            o = 5;
            let _ = o;
        }
        None => {}
    }
}
"#;
    let r = verify(code, "peel2");
    let msg = err_message(&r);
    println!("corner_match_arm_mut_rebind_of_param => {r:?}");
    assert!(
        !msg.contains("not marked mutable"),
        "match-arm mut-rebound param assignment falsely fires rule 2: {r:?}"
    );
}

// while-let rebind (also untracked?).
#[test]
fn corner_while_let_mut_rebind_of_param() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn drain(o: Option<u64>) {
    while let Some(mut o) = o {
        o = 0;
        let _ = o;
        break;
    }
}
"#;
    let r = verify(code, "drain");
    let msg = err_message(&r);
    println!("corner_while_let_mut_rebind_of_param => {r:?}");
    assert!(
        !msg.contains("not marked mutable"),
        "while-let mut-rebound param assignment falsely fires rule 2: {r:?}"
    );
}

// Field assignment through a param must NOT hit rule 2 (bare-path only).
#[test]
fn corner_proof_param_field_assignment_not_bare_path() {
    let code = r#"
struct S {
    f: u64,
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn poke(s: S) {
    s.f = 1;
}
"#;
    let r = verify(code, "poke");
    let msg = err_message(&r);
    assert!(
        !msg.contains("not marked mutable"),
        "field assignment must not hit the bare-path param rule, got {r:?}"
    );
}
