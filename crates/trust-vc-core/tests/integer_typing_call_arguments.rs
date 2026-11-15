//! A call argument is bound at its parameter's type only where that type
//! HOLDS the argument's value (design-trust-proof-backend.md §5b rule 6, the
//! call-argument clause): an argument of the parameter's type as is; a literal
//! (suffixed or not) whose value the parameter type holds, at that type; a
//! fixed-width argument whose every value the parameter type holds, widened
//! by ITS OWN sign; a fixed-width argument at an `int` parameter (an unsigned
//! one at `nat`), lifted to the integer it denotes. Anything else is refused
//! (`Unknown`): Rust and Verus reject such a call, and no reading of it is
//! the value the caller wrote.
//!
//! Measured before this rule (r5 re-verification): `inc32(255u8) == 0` came
//! back `Verified` for `spec fn inc32(x: i32) -> int { x + 1 }` (here
//! `inc32i`; also `!= 256`, and `inc32i(a)` for `a: u8 == 255`) — the `u8`
//! argument's 8-bit term was substituted into `x + 1`, which then wrapped at
//! 8 bits, while rules 3 (the argument is pinned at its parameter's type) and
//! 8 (an `int`-result body is exact) both give 256; and a literal the
//! parameter type cannot hold was wrapped when negative (`id8s(-1) == 255`)
//! but kept exact when too large (`id8s(300) == 300`).
//!
//! `rule_false_*` must not be `Verified`, `rule_true_*` must not be refuted
//! (and must be decided), `refused_*` must be `Unknown`.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::spec]
fn inc32(x: u32) -> int {
    x + 1
}

#[trust_vc::spec]
fn inc32w(x: u32) -> u32 {
    x + 1
}

#[trust_vc::spec]
fn inc32i(x: i32) -> int {
    x + 1
}

#[trust_vc::spec]
fn inc16s(x: i16) -> int {
    x + 1
}

#[trust_vc::spec]
fn id8s(x: u8) -> int {
    x
}

#[trust_vc::spec]
fn idn(x: nat) -> int {
    x
}

#[trust_vc::spec]
fn idi(x: int) -> int {
    x
}

// ---- a u8 argument at a u32 parameter: u32 holds 255, so x == 255 and x + 1 == 256
#[trust_vc::proof]
#[trust_vc::ensures(inc32(255u8) == 0)]
fn rule_false_inc32_u8_literal_eq_0() {}

#[trust_vc::proof]
#[trust_vc::ensures(inc32(255u8) == 256)]
fn rule_true_inc32_u8_literal_eq_256() {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32(a) == 0)]
fn rule_false_inc32_u8_var_eq_0(a: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32(a) == 256)]
fn rule_true_inc32_u8_var_eq_256(a: u8) {}

#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32(a) == 256)]
fn rule_true_inc32_u8_var_exec_eq_256(a: u8) {}

// ---- the r5 re-verifier's case: a u8 argument at an i32 parameter,
// `inc32i(255u8) == 0` came back Verified (8-bit wrap); i32 holds 255
#[trust_vc::proof]
#[trust_vc::ensures(inc32i(255u8) == 0)]
fn rule_false_inc32i_u8_literal_eq_0() {}

#[trust_vc::proof]
#[trust_vc::ensures(inc32i(255u8) == 256)]
fn rule_true_inc32i_u8_literal_eq_256() {}

#[trust_vc::proof]
#[trust_vc::ensures(inc32i(255u8) != 256)]
fn rule_false_inc32i_u8_literal_ne_256() {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32i(a) == 0)]
fn rule_false_inc32i_u8_var_eq_0(a: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32i(a) == 256)]
fn rule_true_inc32i_u8_var_eq_256(a: u8) {}

// u32 result: 255 + 1 in u32 is 256 too
#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32w(a) == 0)]
fn rule_false_inc32w_u8_var_eq_0(a: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(inc32w(a) == 256)]
fn rule_true_inc32w_u8_var_eq_256(a: u8) {}

// ---- a u8 argument at an i16 parameter: zero-extended (its own sign), 200 + 1
#[trust_vc::proof]
#[trust_vc::requires(a == 200)]
#[trust_vc::ensures(inc16s(a) == -55)]
fn rule_false_inc16s_u8_var_sign_extended(a: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == 200)]
#[trust_vc::ensures(inc16s(a) == 201)]
fn rule_true_inc16s_u8_var_eq_201(a: u8) {}

// ---- an i8 argument at an i16 parameter: sign-extended (its own sign)
#[trust_vc::proof]
#[trust_vc::requires(a == -1)]
#[trust_vc::ensures(inc16s(a) == 0)]
fn rule_true_inc16s_i8_var_eq_0(a: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == -1)]
#[trust_vc::ensures(inc16s(a) == 256)]
fn rule_false_inc16s_i8_var_zero_extended(a: i8) {}

// ---- fixed-width arguments lift into int / nat parameters
#[trust_vc::proof]
#[trust_vc::requires(a == -1)]
#[trust_vc::ensures(idi(a) == -1)]
fn rule_true_idi_i8_var_eq_neg1(a: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(a == 255)]
#[trust_vc::ensures(idn(a) == 255)]
fn rule_true_idn_u8_var_eq_255(a: u8) {}

// ---- literals at a u8 parameter: only a value u8 holds is bound
#[trust_vc::proof]
#[trust_vc::ensures(id8s(255) == 255)]
fn rule_true_id8s_255_eq_255() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(-1) == 255)]
fn refused_id8s_neg1_eq_255() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(-1) == -1)]
fn refused_id8s_neg1_eq_neg1() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(300) == 300)]
fn refused_id8s_300_eq_300() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(300) == 44)]
fn refused_id8s_300_eq_44() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(-1) != 7)]
fn refused_id8s_neg1_ne_7() {}

#[trust_vc::requires(true)]
#[trust_vc::ensures(id8s(-1) == 255)]
fn refused_id8s_neg1_exec_eq_255() {}

// ---- typed arguments a u8 parameter cannot hold
#[trust_vc::proof]
#[trust_vc::requires(b == -1)]
#[trust_vc::ensures(id8s(b) == 255)]
fn refused_id8s_i16_var_eq_255(b: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(b == 7)]
#[trust_vc::ensures(id8s(b) == 7)]
fn refused_id8s_u16_var_eq_7(b: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(b == -1)]
#[trust_vc::ensures(idn(b) == 255)]
fn refused_idn_i8_var_eq_255(b: i8) {}

// ---- a suffixed literal whose VALUE the parameter holds
#[trust_vc::proof]
#[trust_vc::ensures(id8s(255u16) == 255)]
fn rule_true_id8s_u16_literal_255_eq_255() {}

#[trust_vc::proof]
#[trust_vc::ensures(id8s(-1i16) == 255)]
fn refused_id8s_i16_literal_neg1_eq_255() {}
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
    let path = dir.join("call_argument_probes.rs");
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
fn call_arguments_are_bound_only_at_a_type_that_holds_them() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            n.starts_with("rule_true_") || n.starts_with("rule_false_") || n.starts_with("refused_")
        })
        .collect();
    assert!(names.len() >= 30, "probe list truncated: {names:?}");
    let mut wrong = Vec::new();
    for func in names {
        let r = run_source(func);
        let got = verdict(&r);
        let raw: String = format!("{r:?}").chars().take(220).collect();
        println!("SRC|{func}|{got}|{raw}");
        let ok = if func.starts_with("rule_true_") {
            got == "Verified"
        } else if func.starts_with("rule_false_") {
            got == "Refuted"
        } else {
            got == "Unknown"
        };
        if !ok {
            wrong.push(format!("{func}: {got}"));
        }
    }
    println!("SUMMARY wrong={wrong:?}");
    assert!(
        wrong.is_empty(),
        "against the call-argument rule: {wrong:#?}"
    );
}
