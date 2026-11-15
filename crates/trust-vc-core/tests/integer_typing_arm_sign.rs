//! A conditional's arms are each widened by THEIR OWN sign
//! (design-trust-proof-backend.md §5b rule 1 and rule 6's `match` clause).
//!
//! `match s { 0 => y_i16, _ => x_u8 }` is typed `i16` (its first non-`i32`
//! arm in the source lowering; the declared type in the typed seam), and every
//! value of `u8` is a value of `i16`, so `derive_arms_int_type` keeps `i16`
//! and each arm denotes the integer it holds: `x == 200` reads 200. The
//! encoder built the ite chain from the LAST arm backwards and widened the
//! accumulated later arms by the MATCH's sign — so the `u8` 200 was
//! sign-extended into the `i16` -56: `== -56` came back `Verified` and the
//! true `== 200` was refuted. Reached through every surface below; the arm
//! order is load-bearing (the `u8`-first order is typed `int` and was right).
//!
//! `never_*` goals are false under every reading on offer (the exact integer,
//! the declared type, each arm's own type): none may be `Verified`.
//! `rule_true_*` goals are §5b's reading (each arm the integer it denotes):
//! none may be refuted. `Unknown` is fail-closed and tolerated, but every
//! `rule_true_*` case is asserted DECIDED so the file cannot pass by deciding
//! nothing.

use std::io::Write;
use trust_vc_core::ir::{CompareOp, MatchArm, MatchPattern, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::spec]
fn pk16(s: u8, y: i16, x: u8) -> i16 {
    match s { 0 => y, _ => x }
}

// ---- spec fn -> i16
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures(pk16(s, y, x) == -56)]
fn never_specfn_i16_reads_neg56(s: u8, y: i16, x: u8) {}

#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures(pk16(s, y, x) == 200)]
fn rule_true_specfn_i16_reads_200(s: u8, y: i16, x: u8) {}

// ---- inline, proof-fn ensures
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == -56)]
fn never_proof_ensures_neg56(s: u8, y: i16, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == 200)]
fn rule_true_proof_ensures_200(s: u8, y: i16, x: u8) {}

// ---- inline, exec-fn ensures
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == -56)]
fn never_exec_ensures_neg56(s: u8, y: i16, x: u8) {}

#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == 200)]
fn rule_true_exec_ensures_200(s: u8, y: i16, x: u8) {}

// ---- proof-fn let
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn never_proof_let_neg56(s: u8, y: i16, x: u8) {
    let m = match s { 0 => y, _ => x };
    trust_vc::assert!(m == -56);
}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn rule_true_proof_let_200(s: u8, y: i16, x: u8) {
    let m = match s { 0 => y, _ => x };
    trust_vc::assert!(m == 200);
}

// ---- exec-fn let
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn never_exec_let_neg56(s: u8, y: i16, x: u8) {
    let m = match s { 0 => y, _ => x };
    trust_vc::assert!(m == -56);
}

#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn rule_true_exec_let_200(s: u8, y: i16, x: u8) {
    let m = match s { 0 => y, _ => x };
    trust_vc::assert!(m == 200);
}

// ---- proof-fn assert of the inline match
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn never_proof_assert_neg56(s: u8, y: i16, x: u8) {
    trust_vc::assert!((match s { 0 => y, _ => x }) == -56);
}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
fn rule_true_proof_assert_200(s: u8, y: i16, x: u8) {
    trust_vc::assert!((match s { 0 => y, _ => x }) == 200);
}

// ---- a guarded arm between them
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, t if t > 0 => x, _ => y }) == -56)]
fn never_guarded_arm_neg56(s: u8, y: i16, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, t if t > 0 => x, _ => y }) == 200)]
fn rule_true_guarded_arm_200(s: u8, y: i16, x: u8) {}

// ---- three arms
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, 1 => x, _ => y }) == -56)]
fn never_three_arms_neg56(s: u8, y: i16, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => y, 1 => x, _ => y }) == 200)]
fn rule_true_three_arms_200(s: u8, y: i16, x: u8) {}

// ---- an enum scrutinee
enum Sel {
    A,
    B,
}

#[trust_vc::proof]
#[trust_vc::requires(matches!(e, Sel::B))]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match e { Sel::A => y, Sel::B => x }) == -56)]
fn never_enum_scrutinee_neg56(e: Sel, y: i16, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(matches!(e, Sel::B))]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match e { Sel::A => y, Sel::B => x }) == 200)]
fn rule_true_enum_scrutinee_200(e: Sel, y: i16, x: u8) {}

// ---- i128 beside u8: 255 must not read -1
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == -1)]
fn never_i128_u8_reads_neg1(s: u8, y: i128, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == 255)]
fn rule_true_i128_u8_reads_255(s: u8, y: i128, x: u8) {}

// ---- i32 beside u16: 65535 must not read -1
#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 65535)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == -1)]
fn never_i32_u16_reads_neg1(s: u8, y: i32, x: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 65535)]
#[trust_vc::ensures((match s { 0 => y, _ => x }) == 65535)]
fn rule_true_i32_u16_reads_65535(s: u8, y: i32, x: u16) {}

// ---- the other arm order (typed `int`, each arm lifted): a control
#[trust_vc::proof]
#[trust_vc::requires(s == 0)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((match s { 0 => x, _ => y }) == 200)]
fn rule_true_u8_first_200(s: u8, y: i16, x: u8) {}

// ---- the conditional twin (`if`): each branch its own sign
#[trust_vc::proof]
#[trust_vc::requires(!c)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((if c { y } else { x }) == -56)]
fn never_ite_neg56(c: bool, y: i16, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(!c)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures((if c { y } else { x }) == 200)]
fn rule_true_ite_200(c: bool, y: i16, x: u8) {}
"####;

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
        _ => "Unknown",
    }
}

fn run_source(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join("arm_sign_probes.rs");
    let mut f = std::fs::File::create(&path).expect("create probe source");
    f.write_all(SRC.as_bytes()).expect("write probe source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

#[test]
fn source_match_arms_keep_their_own_sign() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("rule_true_"))
        .collect();
    assert!(names.len() >= 25, "probe list truncated: {names:?}");
    let mut wrong = Vec::new();
    let mut undecided = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("SRC|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("rule_true_") && got == "Refuted" {
            wrong.push(format!("FALSE COUNTEREXAMPLE {func}"));
        }
        if func.starts_with("rule_true_") && got == "Unknown" {
            undecided.push(func);
        }
    }
    println!("SUMMARY wrong={wrong:?} undecided={undecided:?}");
    assert!(wrong.is_empty(), "wrong verdicts: {wrong:#?}");
    assert!(
        undecided.is_empty(),
        "undecided rule_true cases: {undecided:?}"
    );
}

// ---------------------------------------------------------------------------
// Typed seam (`VerificationContext::from_typed_parts`).
// ---------------------------------------------------------------------------

fn int(w: u32) -> TrustVcType {
    TrustVcType::Int { width: w }
}
fn uint(w: u32) -> TrustVcType {
    TrustVcType::Uint { width: w }
}
fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}
fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}
fn eq(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(l),
        right: Box::new(r),
    }
}

struct SeamCase {
    name: String,
    /// The goal is true (must not be refuted) or false (must not verify).
    truth: bool,
    params: Vec<(String, TrustVcType)>,
    requires: Vec<TrustVcExpr>,
    goal: TrustVcExpr,
    exec: bool,
}

fn run_seam(c: &SeamCase) -> VerifyResult {
    let mut variables: Vec<VariableDecl> = c
        .params
        .iter()
        .map(|(n, t)| VariableDecl::new(n.clone(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = c
        .requires
        .iter()
        .enumerate()
        .map(|(i, r)| TypedProofObligation::requires(format!("arm_requires_{i}"), r.clone()))
        .collect();
    obligations.push(if c.exec {
        TypedProofObligation::assert("arm_goal", c.goal.clone())
    } else {
        TypedProofObligation::ensures("arm_goal", c.goal.clone())
    });
    let mut ctx = VerificationContext::from_typed_parts(variables, obligations);
    if c.exec {
        ctx.enable_overflow_checks();
    }
    ctx.verify()
}

/// `match s { arms }` over a `u8` scrutinee pinned to `pick`, where arm `k`
/// is pattern `k` (the last one `_`) and body `bodies[k]`.
fn seam_match(bodies: &[TrustVcExpr], decl: &TrustVcType) -> TrustVcExpr {
    let last = bodies.len() - 1;
    TrustVcExpr::Match {
        scrutinee: Box::new(var("s", uint(8))),
        arms: bodies
            .iter()
            .enumerate()
            .map(|(k, body)| {
                let pattern = if k == last {
                    MatchPattern::Wildcard
                } else {
                    MatchPattern::Lit(lit(i128::try_from(k).expect("small"), uint(8)))
                };
                MatchArm::new(pattern, body.clone())
            })
            .collect(),
        ty: decl.clone(),
    }
}

fn seam_cases() -> Vec<SeamCase> {
    let mut v = Vec::new();
    // (wide signed type, narrow unsigned type, narrow value, its wrong
    // sign-extended reading)
    let pairs = [
        (int(16), uint(8), 200, -56),
        (int(32), uint(16), 65535, -1),
        (int(128), uint(8), 255, -1),
        (int(64), uint(32), 4_294_967_295, -1),
    ];
    for (wide, narrow, value, wrong) in pairs {
        let w = || var("w", wide.clone());
        let n = || var("n", narrow.clone());
        let tag = format!("{}_{}", wide.to_type_string(), narrow.to_type_string());
        // (arm bodies, index of the arm `s` selects)
        let shapes: Vec<(&str, Vec<TrustVcExpr>, i128)> = vec![
            ("wide_first", vec![w(), n()], 1),
            ("three_arms", vec![w(), n(), w()], 1),
            ("narrow_middle_of_four", vec![w(), w(), n(), w()], 2),
            ("narrow_first", vec![n(), w()], 0),
        ];
        for (shape, bodies, pick) in shapes {
            for exec in [false, true] {
                let params = vec![
                    ("s".to_string(), uint(8)),
                    ("w".to_string(), wide.clone()),
                    ("n".to_string(), narrow.clone()),
                ];
                let requires = vec![
                    eq(var("s", uint(8)), lit(pick, uint(8))),
                    eq(n(), lit(value, narrow.clone())),
                ];
                let m = seam_match(&bodies, &wide);
                let mode = if exec { "exec" } else { "spec" };
                v.push(SeamCase {
                    name: format!("seam_{tag}_{shape}_eq_{wrong}[{mode}]"),
                    truth: false,
                    params: params.clone(),
                    requires: requires.clone(),
                    goal: eq(m.clone(), lit(wrong, wide.clone())),
                    exec,
                });
                v.push(SeamCase {
                    name: format!("seam_{tag}_{shape}_eq_{value}[{mode}]"),
                    truth: true,
                    params,
                    requires,
                    goal: eq(m, lit(value, wide.clone())),
                    exec,
                });
            }
        }
    }
    v
}

#[test]
fn typed_seam_match_arms_keep_their_own_sign() {
    let mut wrong = Vec::new();
    let mut undecided = Vec::new();
    for c in seam_cases() {
        let r = run_seam(&c);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(200).collect();
        println!("SEAM|{}|truth={}|{got}|{raw}", c.name, c.truth);
        match (c.truth, got) {
            (false, "Verified") => wrong.push(format!("FALSE VERIFIED {}", c.name)),
            (true, "Refuted") => wrong.push(format!("FALSE COUNTEREXAMPLE {}", c.name)),
            (true, "Unknown") => undecided.push(c.name.clone()),
            _ => {}
        }
    }
    println!("SUMMARY wrong={wrong:?} undecided={undecided:?}");
    assert!(wrong.is_empty(), "wrong verdicts: {wrong:#?}");
    assert!(undecided.is_empty(), "undecided true cases: {undecided:?}");
}
