//! A `nat` holds only non-negative values (design-trust-proof-backend.md §5b
//! rule 6), at every binding site: a body `let`, a spec function's result, a
//! call argument.
//!
//! Measured before (r9 verifier, identical at 44e93f72 and 50b27076):
//! * `derive_binary_int_type` returned a DECLARED `nat` whatever the other
//!   operand was, so `nat + int` and `nat / int` were typed `nat`: `let v: nat
//!   = x1 + x2` (`x1 == 7`, `x2 == -9`) held -2 (`v == -2` Verified), and the
//!   committed oracle's OWN default seed (`0x06_ac1e_0924`, source BodyProof
//!   case 52) decided `let v: nat = x1 / x2` (`x2: int`), which §5b refuses;
//! * `int_binding` bound ANY untyped literal at a `nat` as the exact integer:
//!   `spec fn gneg() -> nat { -1 }` verified `gneg() == -1`, and `let v: nat
//!   = -1; v == -1` was `Verified`.
//!
//! A difference or a negation of `nat`s is an `int` too (`0 - 1`, `-1` are not
//! `nat`s); a sum, product, quotient or remainder of two `nat`s stays `nat`.
//!
//! `never_*` must not be `Verified`; `refused_*` must be `Unknown`;
//! `verified_*` (a well-typed binding) must be `Verified`.

use std::io::Write;
use trust_vc_core::ir::{ArithOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
use trust_vc_types::Seq;

#[trust_vc::spec]
fn gneg() -> nat {
    -1
}

#[trust_vc::proof]
#[trust_vc::ensures(gneg() == -1)]
fn refused_nat_result_neg1() {}

#[trust_vc::spec]
fn gdiff(a: nat, b: nat) -> nat {
    a - b
}

#[trust_vc::proof]
#[trust_vc::ensures(gdiff(0, 1) == -1)]
fn refused_nat_result_difference() {}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn refused_nat_let_neg1() {
    let v: nat = -1;
    trust_vc::assert!(v == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 7)]
#[trust_vc::requires(x2 == -9)]
#[trust_vc::ensures(true)]
fn refused_nat_let_from_nat_plus_int(x1: nat, x2: int) {
    let v: nat = x1 + x2;
    trust_vc::assert!(v == -2);
}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 0)]
#[trust_vc::requires(x2 == 1)]
#[trust_vc::ensures(true)]
fn refused_nat_let_from_nat_minus_nat(x1: nat, x2: nat) {
    let v: nat = x1 - x2;
    trust_vc::assert!(v == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 1)]
#[trust_vc::ensures(true)]
fn refused_nat_let_from_negated_nat(x1: nat) {
    let v: nat = -x1;
    trust_vc::assert!(v == -1);
}

// The committed oracle's own default seed (`0x06_ac1e_0924`), source
// BodyProof case 52: `int` at a `nat` let, decided before.
#[trust_vc::proof]
#[trust_vc::requires(x0 == 11790472795156548667)]
#[trust_vc::requires(x1 == 196604)]
#[trust_vc::requires(x2 == -170141183460469231731687303715884105727)]
#[trust_vc::requires(x3 == 59607)]
#[trust_vc::ensures(true)]
fn refused_oracle_default_seed_case_52(x0: u64, x1: nat, x2: int, x3: u16) {
    let v: nat = (x1 / x2);
    trust_vc::assert!(v > x3);
}

#[trust_vc::requires(a >= b)]
#[trust_vc::ensures(result + b == a)]
fn refused_exec_nat_result_difference(a: nat, b: nat) -> nat {
    a - b
}

#[trust_vc::requires(a >= b)]
#[trust_vc::ensures(result + b == a)]
fn verified_exec_nat_result_difference_cast(a: nat, b: nat) -> nat {
    (a - b) as nat
}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 7)]
#[trust_vc::requires(x2 == 9)]
#[trust_vc::ensures(true)]
fn verified_nat_let_from_nat_plus_nat(x1: nat, x2: nat) {
    let v: nat = x1 + x2 * 2 + 1;
    trust_vc::assert!(v == 26);
}

#[trust_vc::spec]
fn gsum(a: nat, b: nat) -> nat {
    a + b + 1
}

#[trust_vc::proof]
#[trust_vc::ensures(gsum(2, 3) == 6)]
fn verified_nat_result_sum() {}
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
    let path = dir.join("integer_typing_nat_bindings.rs");
    let mut f = std::fs::File::create(&path).expect("create source");
    f.write_all(SRC.as_bytes()).expect("write source");
    drop(f);
    verify_function_from_file(path.to_str().expect("utf-8 path"), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn judge(func: &str, got: &str, wrong: &mut Vec<String>) {
    if func.starts_with("never_") && got == "Verified" {
        wrong.push(format!("FALSE VERIFIED {func}"));
    }
    if func.starts_with("refused_") && got != "Unknown" {
        wrong.push(format!("DECIDED A REFUSED BINDING {func}: {got}"));
    }
    if func.starts_with("verified_") && got != "Verified" {
        wrong.push(format!("NOT VERIFIED {func}: {got}"));
    }
}

#[test]
fn a_nat_binding_holds_only_non_negative_values_source() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            n.starts_with("never_") || n.starts_with("refused_") || n.starts_with("verified_")
        })
        .collect();
    assert_eq!(names.len(), 11, "case list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("NAT|{func}|{got}|{raw}");
        judge(func, got, &mut wrong);
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The typed seam: a node DECLARED `nat` over a `nat` and an `int` operand
/// is an `int`, so a `let` at `nat` refuses it.
#[test]
fn a_nat_binding_holds_only_non_negative_values_seam() {
    let nat = TrustVcType::Nat;
    let int = TrustVcType::MathInt;
    let var = |name: &str, ty: &TrustVcType| TrustVcExpr::Var {
        name: name.to_string(),
        ty: ty.clone(),
    };
    let lit = |value: i128, ty: &TrustVcType| TrustVcExpr::IntLit {
        value,
        ty: ty.clone(),
    };
    let eq = |l: TrustVcExpr, r: TrustVcExpr| TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(l),
        right: Box::new(r),
    };
    let mut wrong = Vec::new();
    for (name, op, right_ty) in [
        ("refused_seam_nat_plus_int_declared_nat", ArithOp::Add, &int),
        ("refused_seam_nat_div_int_declared_nat", ArithOp::Div, &int),
        (
            "refused_seam_nat_minus_nat_declared_nat",
            ArithOp::Sub,
            &nat,
        ),
    ] {
        let value = TrustVcExpr::Arith {
            op,
            left: Box::new(var("x1", &nat)),
            right: Box::new(var("x2", right_ty)),
            ty: nat.clone(),
        };
        let goal = eq(
            TrustVcExpr::Let {
                name: "v".to_string(),
                ty: nat.clone(),
                value: Box::new(value),
                body: Box::new(var("v", &nat)),
            },
            lit(-2, &int),
        );
        let x2 = if *right_ty == nat { 9 } else { -9 };
        let variables = vec![
            VariableDecl::new("x1".to_string(), nat.clone()),
            VariableDecl::new("x2".to_string(), right_ty.clone()),
            VariableDecl::new("result".to_string(), TrustVcType::Bool),
        ];
        let obligations = vec![
            TypedProofObligation::requires("n_requires_0", eq(var("x1", &nat), lit(7, &nat))),
            TypedProofObligation::requires(
                "n_requires_1",
                eq(var("x2", right_ty), lit(x2, right_ty)),
            ),
            TypedProofObligation::ensures("n_goal", goal),
        ];
        let r = VerificationContext::from_typed_parts(variables, obligations).verify();
        let got = verdict(&r);
        println!("NATSEAM|{name}|{got}|{r:?}");
        judge(name, got, &mut wrong);
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
