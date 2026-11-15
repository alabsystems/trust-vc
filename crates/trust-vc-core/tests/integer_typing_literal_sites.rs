//! The value-preserving literal rule (9def8d43) at the
//! lowering sites that do NOT derive their type from their operands — match
//! arms, spec-fn arguments and bodies, `let` with a declared type, array and
//! `seq!` elements, `wrapping_*` arguments.
//!
//! Before 9def8d43 an unsuffixed `-1` beside a `u8` was retyped to the `u8`
//! negation (255, same width); now it keeps its `Int{32}` type. Every goal
//! here is FALSE under every reading of that literal (-1, the `u8` 255, or
//! 300 / 44) — so none may come back Verified.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::spec]
fn idu8(a: u8) -> u8 {
    a
}

#[trust_vc::spec]
fn m1() -> u8 {
    -1
}

#[trust_vc::spec]
fn let_body(y: i16) -> bool {
    let t: u8 = y;
    t > 1000
}

#[trust_vc::spec]
fn let_lit_body() -> bool {
    let t: u8 = -1;
    t > 1000
}

#[trust_vc::spec]
fn let_u16_body() -> bool {
    let t: u16 = -1;
    t > 70000
}

#[trust_vc::spec]
fn let_u8_body_eq() -> bool {
    let t: u8 = -1;
    t == 4294967295
}

#[trust_vc::spec]
fn let_u8_param_body(x: u8) -> bool {
    let t: u8 = -1;
    t > x
}

struct S8 {
    f: u8,
}

#[trust_vc::spec]
fn mk8() -> S8 {
    S8 { f: -1 }
}

#[trust_vc::proof]
#[trust_vc::ensures(let_u16_body())]
fn never_specfn_let_u16_neg_literal() {}

#[trust_vc::proof]
#[trust_vc::ensures(let_u8_body_eq())]
fn never_specfn_let_u8_neg_literal_eq_u32max() {}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(let_u8_param_body(x))]
fn never_specfn_let_u8_neg_literal_gt_255(x: u8) {}

#[trust_vc::requires(true)]
fn never_exec_assert_specfn_let_u8_neg_literal() {
    trust_vc::assert!(let_lit_body());
}

#[trust_vc::proof]
fn never_proof_body_let_u8_neg_literal() {
    let t: u8 = -1;
    trust_vc::assert!(t > 1000);
}

#[trust_vc::proof]
#[trust_vc::ensures(m1() == 7)]
fn never_specfn_body_neg_literal_eq_7() {}

#[trust_vc::requires(true)]
fn never_exec_assert_specfn_body_neg_literal() {
    trust_vc::assert!(m1() > 1000);
}

#[trust_vc::proof]
#[trust_vc::ensures(mk8().f > 1000)]
fn never_struct_field_neg_literal() {}

#[trust_vc::ensures(result > 1000)]
fn never_exec_return_neg_literal() -> u8 {
    -1
}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 0)]
#[trust_vc::ensures((match s { 0 => x, _ => -1 }) > 1000)]
fn never_match_arm_neg_literal(s: u8, x: u8) {}

#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 0)]
#[trust_vc::ensures((match s { 0 => x, _ => -1 }) > 1000)]
fn never_match_arm_neg_literal_exec(s: u8, x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 0)]
#[trust_vc::ensures((match s { 0 => x, _ => 300 }) > 1000)]
fn never_match_arm_300_literal(s: u8, x: u8) {}

#[trust_vc::proof]
#[trust_vc::ensures(idu8(-1) > 1000)]
fn never_specfn_arg_neg_literal() {}

#[trust_vc::proof]
#[trust_vc::ensures(idu8(300) > 1000)]
fn never_specfn_arg_300_literal() {}

#[trust_vc::proof]
#[trust_vc::ensures(m1() > 1000)]
fn never_specfn_body_neg_literal() {}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(let_body(y))]
fn never_specfn_let_u8_from_i16(y: i16) {}

#[trust_vc::proof]
#[trust_vc::ensures(let_lit_body())]
fn never_specfn_let_u8_neg_literal() {}

fn never_exec_let_u8_neg_literal() {
    let t: u8 = -1;
    trust_vc::assert!(t > 1000);
}

#[trust_vc::requires(x == 0)]
fn never_array_elem_neg_literal(x: u8) {
    let a: [u8; 2] = [x, -1];
    trust_vc::assert!(a[1] > 1000);
}

#[trust_vc::proof]
#[trust_vc::ensures(seq![0u8, -1][1] > 1000)]
fn never_seq_elem_neg_literal() {}

#[trust_vc::requires(x == 0)]
#[trust_vc::ensures(x.wrapping_add(-1) > 1000)]
fn never_wrapping_add_neg_literal(x: u8) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::ensures(x.wrapping_add(300) > 1000)]
fn never_wrapping_add_300_literal(x: u8) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::ensures(x.wrapping_sub(1) == 255)]
fn control_wrapping_sub_one(x: u8) {}

#[trust_vc::requires(c)]
#[trust_vc::requires(x == 0)]
#[trust_vc::ensures((if !c { x } else { -1 }) == -1)]
fn control_ite_neg_literal(c: bool, x: u8) {}
"####;

fn run(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("literal_sites.rs");
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

#[test]
fn literal_sites_never_rebind_a_value() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| n.starts_with("never_") || n.starts_with("control_"))
        .collect();
    let mut never_verified = Vec::new();
    let mut control_failed = Vec::new();
    for func in names {
        let r = run(func);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        let got = match &r {
            VerifyResult::Verified => "Verified",
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
            _ => "Unknown",
        };
        println!("LIT|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            never_verified.push(func);
        }
        if func.starts_with("control_") && got == "Refuted" {
            control_failed.push(func);
        }
    }
    println!("SUMMARY never_verified={never_verified:?}");
    println!("SUMMARY control_refuted={control_failed:?}");
    assert!(
        never_verified.is_empty() && control_failed.is_empty(),
        "FALSE VERIFIED {never_verified:?}; FALSE COUNTEREXAMPLE {control_failed:?}"
    );
}
