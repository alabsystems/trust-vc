//! SOURCE-frontend probes (`verify_function_from_file`,
//! Verus-style `requires`/`ensures`, exec fns, proof fns, spec fns).
//!
//! `NEVER_*` goals are FALSE under every reading on offer (the exact
//! integers, two's complement in any operand's type or in the type the old
//! lowering copied from the left operand), so none may be Verified.
//! `RULE_*` goals are decided by design-trust-proof-backend.md §5b alone
//! (named per case); their verdicts are reported and asserted separately.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
// ---- match over arms of two types (x: u8 == 0, y: i16 == -1): -1 / 255, never >= 256
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures((match s { 0 => x, _ => y }) >= z)]
fn never_match_mixed_arms_ge(s: u8, x: u8, y: i16, z: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(s == 1)]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures((match s { 0 => x, _ => y }) >= z)]
fn never_match_mixed_arms_ge_proof(s: u8, x: u8, y: i16, z: i16) {}

#[trust_vc::requires(c == false)]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::requires(z == 256)]
#[trust_vc::ensures((match c { true => x, false => y }) >= z)]
fn never_match_bool_mixed_arms_ge(c: bool, x: u8, y: i16, z: i16) {}

// ---- wrapping/saturating methods over a mixed pair: 255 / -1 / 0, never > 1000
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x.wrapping_add(y) > 1000)]
fn never_wrapping_add_mixed(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x.saturating_add(y) > 1000)]
fn never_saturating_add_mixed(x: u8, y: i16) {}

// ---- shift / cast / bitwise-not of a mixed sum
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(((x + y) << 1u32) > 1000)]
fn never_shl_of_mixed_sum(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(((x + y) as u32) == 65535)]
fn never_cast_of_mixed_sum(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(!(x + y) != 0)]
fn never_not_of_mixed_sum(x: u8, y: i16) {}

// ---- nat subtraction (Verus: nat - nat is int): 0 - 1 = -1
#[trust_vc::proof]
#[trust_vc::requires(n == 0)]
#[trust_vc::ensures(n - 1 > 300)]
fn never_nat_minus_one_gt_300(n: nat) {}

#[trust_vc::proof]
#[trust_vc::requires(n == 0)]
#[trust_vc::requires(n - 1 <= 1000)]
#[trust_vc::ensures(n == 7)]
fn never_nat_premise_vacuity(n: nat) {}

#[trust_vc::proof]
#[trust_vc::requires(n == 0)]
#[trust_vc::ensures(n - 1 >= 0)]
fn rule_false_nat_minus_one_ge_0(n: nat) {}

// ---- let bindings over a mixed sum / an ill-typed narrowing let
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
fn never_let_mixed_sum_assert(x: u8, y: i16) {
    let s = x + y;
    trust_vc::assert!(s > 1000);
}

#[trust_vc::requires(y == -1)]
fn never_let_u8_from_i16_assert(y: i16) {
    let s: u8 = y;
    trust_vc::assert!(s > 1000);
}

// ---- an i32-suffixed literal beside a u8 (rule 1: two fixed types -> exact 300)
#[trust_vc::proof]
#[trust_vc::requires(x == 100)]
#[trust_vc::ensures(x + 200i32 == 44)]
fn rule_false_u8_plus_i32_suffixed_eq_44(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 100)]
#[trust_vc::ensures(x + 200i64 == 44)]
fn control_u8_plus_i64_suffixed_eq_44(x: u8) {}

// ---- an untyped tree beside an `int` (Verus: int arithmetic, 2147483648)
#[trust_vc::proof]
#[trust_vc::requires(z == -2147483648)]
#[trust_vc::ensures(z == 2147483647 + 1)]
fn rule_int_peer_tree_wraps(z: int) {}

// ---- var-to-var pin across types, proof fn (spec arithmetic in u8 wraps: 0)
#[trust_vc::proof]
#[trust_vc::requires(y == 200)]
#[trust_vc::requires(x == y)]
#[trust_vc::ensures(x + 56u8 == 256)]
fn rule_false_pin_x_eq_y_u8_sum_256(x: u8, y: i16) {}

// ---- exec: shift by the width and division by zero panic in Rust
#[trust_vc::requires(k == 8)]
fn rule_false_exec_shl_by_width(k: u32) {
    trust_vc::assert!((1u8 << k) == 0);
}

#[trust_vc::requires(x == 5)]
#[trust_vc::requires(w == 0)]
fn rule_false_exec_div_by_zero(x: u8, w: u8) {
    trust_vc::assert!(x / w == 0);
}

// ---- negating an unsigned value: 255 / -1, never > 1000
#[trust_vc::proof]
#[trust_vc::requires(x == 1)]
#[trust_vc::ensures(-x > 1000)]
fn never_neg_u8(x: u8) {}

// ---- spec fn returning a mixed sum at a declared u8 result
#[trust_vc::spec]
fn mixsum(x: u8, y: i16) -> u8 {
    x + y
}

#[trust_vc::proof]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(mixsum(x, y) > 1000)]
fn never_specfn_mixed_body(x: u8, y: i16) {}

// ---- u8::MAX + a negative i16 (IntConst beside a mixed operand)
#[trust_vc::proof]
#[trust_vc::requires(y == -300)]
#[trust_vc::ensures(u8::MAX + y > 0)]
fn never_u8max_plus_neg_i16(y: i16) {}

// ---- chained mixed arithmetic (u8 wrap inside, exact outside):
//      x + w == 44 in u8, then + z (i16 0) -> 44; exact 300
#[trust_vc::proof]
#[trust_vc::requires(x == 200)]
#[trust_vc::requires(w == 100)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures((x + w) + z == 300)]
fn rule_false_nested_wrap_then_exact(x: u8, w: u8, z: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 200)]
#[trust_vc::requires(w == 100)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures((x + w) + z == 44)]
fn rule_true_nested_wrap_then_exact(x: u8, w: u8, z: i16) {}

// ---- mixed exec: the u8 part overflows before the mixed add (exec ensures)
#[trust_vc::requires(x == 200)]
#[trust_vc::requires(w == 100)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures((x + w) + z == 44)]
fn rule_false_exec_nested_overflow(x: u8, w: u8, z: i16) {}

// ---- more wrapping methods over a mixed pair: 255 / -1, never > 1000
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == 1)]
#[trust_vc::ensures(x.wrapping_sub(y) > 1000)]
fn never_wrapping_sub_mixed(x: u8, y: i16) {}

#[trust_vc::requires(x == 1)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x.wrapping_mul(y) > 1000)]
fn never_wrapping_mul_mixed(x: u8, y: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x.wrapping_add(y) > 1000)]
fn never_wrapping_add_mixed_proof(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
fn never_wrapping_add_mixed_bv(x: u8, y: i16) {
    trust_vc::assert_by_bit_vector! { x.wrapping_add(y) > 1000u16 };
}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
fn never_let_wrapping_mixed_assert(x: u8, y: i16) {
    let s = x.wrapping_add(y);
    trust_vc::assert!(s > 1000);
}

// ---- spec fns whose declared u8 result is fed a value of another type
#[trust_vc::spec]
fn idu8(a: u8) -> u8 {
    a
}

#[trust_vc::proof]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(idu8(y) > 1000)]
fn never_call_u8_specfn_with_i16(y: i16) {}

#[trust_vc::spec]
fn pick(c: bool, x: u8, y: i16) -> u8 {
    if c { x } else { y }
}

#[trust_vc::proof]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(pick(false, x, y) > 1000)]
fn never_specfn_mixed_ite_body(x: u8, y: i16) {}

#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
fn never_specfn_mixed_body_exec_assert(x: u8, y: i16) {
    trust_vc::assert!(mixsum(x, y) > 1000);
}

#[trust_vc::proof]
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(mixsum(x, y) == 65535)]
fn never_specfn_mixed_body_eq_65535(x: u8, y: i16) {}

// control: must verify
#[trust_vc::requires(x == 0)]
#[trust_vc::requires(y == -1)]
#[trust_vc::ensures(x + y == -1)]
fn control_mixed_sum(x: u8, y: i16) {}
"####;

fn run(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("source_probes.rs");
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
fn source_frontend_probes() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| !["mixsum", "idu8", "pick"].contains(n))
        .collect();
    let mut never_verified = Vec::new();
    let mut rule_wrong = Vec::new();
    for func in names {
        let r = run(func);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        let got = match &r {
            VerifyResult::Verified => "Verified",
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => "Refuted",
            _ => "Unknown",
        };
        println!("SRC|{func}|{got}|{raw}");
        if func.starts_with("never_") && got == "Verified" {
            never_verified.push(func);
        }
        if (func.starts_with("rule_false_") && got == "Verified")
            || (func.starts_with("rule_true_") && got == "Refuted")
            || (func.starts_with("control_mixed") && got != "Verified")
        {
            rule_wrong.push(func);
        }
    }
    println!("SUMMARY never_verified={never_verified:?}");
    println!("SUMMARY rule_wrong={rule_wrong:?}");
    assert!(
        never_verified.is_empty() && rule_wrong.is_empty(),
        "FALSE VERIFIED {never_verified:?}; against the §5b rule {rule_wrong:?}"
    );
}
