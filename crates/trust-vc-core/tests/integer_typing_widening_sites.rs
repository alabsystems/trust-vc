//! Widening sites other than `match` read the sign of the value they widen
//! (design-trust-proof-backend.md §5b rule 10): a cast reads its operand at
//! the operand's OWN type (not the node's declared `from_ty`), a sequence
//! index is extended by its own sign, a collection element argument is bound
//! at the element type by its own sign, and a body `let` binds its value at
//! its ascribed type (rule 6).
//!
//! `never_*` must not be `Verified`; `must_*` must not be refuted;
//! `refused_*` (a binding at a type that cannot hold its value) must be
//! `Unknown`.

use std::io::Write;
use trust_vc_core::ir::{CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_core::vc::{TypedProofObligation, VariableDecl, VerificationContext};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
        _ => "Unknown",
    }
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

fn run_seam(
    params: &[(&str, TrustVcType)],
    requires: &[TrustVcExpr],
    goal: TrustVcExpr,
) -> VerifyResult {
    let mut variables: Vec<VariableDecl> = params
        .iter()
        .map(|(n, t)| VariableDecl::new((*n).to_string(), t.clone()))
        .collect();
    variables.push(VariableDecl::new("result".to_string(), TrustVcType::Bool));
    let mut obligations: Vec<TypedProofObligation> = requires
        .iter()
        .enumerate()
        .map(|(i, r)| TypedProofObligation::requires(format!("w_requires_{i}"), r.clone()))
        .collect();
    obligations.push(TypedProofObligation::ensures("w_goal", goal));
    VerificationContext::from_typed_parts(variables, obligations).verify()
}

/// A cast whose declared `from_ty` is not its operand's type is a claim the
/// one IR typing validator refuses (§5b rule 13): it was read at the
/// declared `i8` (a `u8` 200 as -56, `Verified`) until 1dc1bada read it at
/// the operand's own type. Declared honestly, the operand is its own value.
#[test]
fn a_cast_reads_its_operand_at_the_operands_own_type() {
    let u8t = TrustVcType::Uint { width: 8 };
    let i8t = TrustVcType::Int { width: 8 };
    let i16t = TrustVcType::Int { width: 16 };
    let cast = |from: &TrustVcType, to: TrustVcType| TrustVcExpr::Cast {
        expr: Box::new(var("x", u8t.clone())),
        from_ty: from.clone(),
        to_ty: to,
    };
    let pin = vec![eq(var("x", u8t.clone()), lit(200, u8t.clone()))];
    let params = [("x", u8t.clone())];
    let mut wrong = Vec::new();
    for (from, claim) in [(&i8t, "lie"), (&u8t, "honest")] {
        for (name, truth, goal) in [
            (
                "never_cast_i16_reads_neg56",
                false,
                eq(cast(from, i16t.clone()), lit(-56, i16t.clone())),
            ),
            (
                "must_cast_i16_reads_200",
                true,
                eq(cast(from, i16t.clone()), lit(200, i16t.clone())),
            ),
            (
                "never_cast_int_reads_neg56",
                false,
                eq(
                    cast(from, TrustVcType::MathInt),
                    lit(-56, TrustVcType::MathInt),
                ),
            ),
            (
                "must_cast_int_reads_200",
                true,
                eq(
                    cast(from, TrustVcType::MathInt),
                    lit(200, TrustVcType::MathInt),
                ),
            ),
        ] {
            let r = run_seam(&params, &pin, goal);
            let got = verdict(&r);
            println!(
                "SEAM|{claim}_{name}|{got}|{:?}",
                format!("{r:?}").chars().take(160).collect::<String>()
            );
            let bad = match claim {
                "lie" => got != "Unknown",
                _ => (!truth && got == "Verified") || (truth && got != "Verified"),
            };
            if bad {
                wrong.push(format!("{claim}_{name}: {got}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:?}");
}

/// A typed-seam `let` whose value its declared type cannot hold is refused
/// even where the pre-solve constant evaluator folds the whole goal: the
/// evaluator substituted the value bare (found by the oracle at seed 1:
/// `let v0: u8 = -764435651; v0 == 1079..478nat` came back a decided
/// counterexample instead of a refusal).
#[test]
fn a_folded_let_binds_its_value_like_the_encoder() {
    let u8t = TrustVcType::Uint { width: 8 };
    let placeholder = TrustVcType::Int { width: 32 };
    let let_of = |value: TrustVcExpr, ty: TrustVcType| TrustVcExpr::Let {
        name: "v".to_string(),
        ty: ty.clone(),
        value: Box::new(value),
        body: Box::new(var("v", ty)),
    };
    let mut wrong = Vec::new();
    // Refused: -764435651 is no `u8`.
    let refused = run_seam(
        &[],
        &[],
        eq(
            let_of(
                TrustVcExpr::Neg(Box::new(lit(764_435_651, placeholder.clone()))),
                u8t.clone(),
            ),
            lit(7, u8t.clone()),
        ),
    );
    println!(
        "SEAM|refused_folded_let_u8_neg|{}|{refused:?}",
        verdict(&refused)
    );
    if verdict(&refused) != "Unknown" {
        wrong.push(format!("refused_folded_let_u8_neg: {}", verdict(&refused)));
    }
    // Bound: 200 is a `u8`, and a `u8` value lifts into an `int` let.
    for (name, truth, goal) in [
        (
            "must_folded_let_u8_200",
            true,
            eq(
                let_of(lit(200, placeholder.clone()), u8t.clone()),
                lit(200, u8t.clone()),
            ),
        ),
        (
            "must_folded_let_int_lifts_255u8",
            true,
            eq(
                let_of(lit(255, u8t.clone()), TrustVcType::MathInt),
                lit(255, TrustVcType::MathInt),
            ),
        ),
        (
            "never_folded_let_int_reads_neg1",
            false,
            eq(
                let_of(lit(255, u8t.clone()), TrustVcType::MathInt),
                lit(-1, TrustVcType::MathInt),
            ),
        ),
    ] {
        let r = run_seam(&[], &[], goal);
        let got = verdict(&r);
        println!("SEAM|{name}|{got}|{r:?}");
        if (truth && got != "Verified") || (!truth && got == "Verified") {
            wrong.push(format!("{name}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:?}");
}

const SRC: &str = r####"
use trust_vc_types::Seq;

// ---- a negative signed index is out of bounds, never element 255
#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(i == -1)]
#[trust_vc::ensures(s[i] == s[255])]
fn never_neg_index_is_element_255(s: Seq<u8>, i: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 300)]
#[trust_vc::requires(i == 7)]
#[trust_vc::ensures(s[i] == s[7])]
fn must_pos_index_is_element_7(s: Seq<u8>, i: i8) {}

// ---- an element argument of a narrower type: widened by its own sign
#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == -1)]
#[trust_vc::requires(x == -1)]
#[trust_vc::ensures(s.contains(x))]
fn must_contains_sign_extended_needle(s: Seq<i64>, x: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == 4294967295)]
#[trust_vc::requires(x == -1)]
#[trust_vc::ensures(s.contains(x))]
fn never_contains_zero_extended_needle(s: Seq<i64>, x: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == 200)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures(s.contains(x))]
fn must_contains_zero_extended_u8_needle(s: Seq<i16>, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s.len() == 1)]
#[trust_vc::requires(s[0] == -56)]
#[trust_vc::requires(x == 200)]
#[trust_vc::ensures(s.contains(x))]
fn never_contains_sign_extended_u8_needle(s: Seq<i16>, x: u8) {}

// ---- a body `let` binds its value AT its ascribed type (§5b rule 6): an
// `int` ascription lifts, so `v + 1` is exact; the substituted value used to
// keep its own type and compute `x + 1` in `u8`
#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn must_body_let_int_lifts(x: u8) {
    let v: int = x;
    trust_vc::assert!(v + 1 == 256);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(true)]
fn never_body_let_int_wraps(x: u8) {
    let v: int = x;
    trust_vc::assert!(v + 1 == 0);
}

// ---- a body `let` of a type that cannot hold the value is refused
#[trust_vc::requires(y == -1)]
fn refused_body_let_u8_from_i16(y: i16) {
    let v: u8 = y;
    trust_vc::assert!(v == -1);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 7)]
#[trust_vc::ensures(true)]
fn refused_body_let_nat_from_i8(x: i8) {
    let v: nat = x;
    trust_vc::assert!(v == 7);
}
"####;

fn run_source(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let path = dir.join("widening_site_probes.rs");
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
fn source_index_and_element_widening_use_the_values_own_sign() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .collect();
    assert_eq!(names.len(), 10, "probe list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(200).collect();
        println!("SRC|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            wrong.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("must_") && got == "Refuted" {
            wrong.push(format!("FALSE COUNTEREXAMPLE {func}"));
        }
        if func.starts_with("refused_") && got != "Unknown" {
            wrong.push(format!("DECIDED A REFUSED BINDING {func}: {got}"));
        }
    }
    println!("SUMMARY wrong={wrong:?}");
    assert!(wrong.is_empty(), "{wrong:#?}");
}
