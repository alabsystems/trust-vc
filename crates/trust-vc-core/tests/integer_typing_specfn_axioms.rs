//! `#[trust_vc::spec]` fn bodies (found by tests/integer_typing_survey.rs,
//! spec-fn modes, default seed, then reduced).
//!
//! * `never_*`: FALSE under every reading (exact, wrap in any operand's type,
//!   wrap in the declared type) — most are contradictions (`f(x) == 0 &&
//!   f(x) == 1`, `ensures(false)`), so a `Verified` means the VC's
//!   assumptions are inconsistent. At 2f792110 a spec fn whose body puts an
//!   `i32` operation beside another integer type (`(x + 1) * 2i64`,
//!   `(x + 1) + y` with `y: i64`, `(x + 1) * 2i64 > 0`) makes EVERY VC that
//!   mentions it prove `false` (the `u32`/`i64`/`u8` analogues do not); an
//!   exec caller of a spec fn dividing an `i16` by a wrapping `u16` product at
//!   the pinned input is vacuous too. At 8bbef1af these are refuted/unknown.
//! * `same_*` pairs: one formula written inline and through a spec fn — the
//!   verdicts must agree. A spec fn returning `int` computes its body's plain
//!   arithmetic exactly (§5b rule 8), so its inline twin is written in the
//!   `int` context too (`same_c`).
//! * `excl_*` pairs: two different values claimed for one call — they must not
//!   both be Verified.
//! * `control_*`: TRUE under every reading; must not be refuted.

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
#[trust_vc::spec]
fn g203(x0: u16) -> int {
    (-(18252i16 / (x0 * 3)))
}

#[trust_vc::spec]
fn q203(x0: u16) -> int {
    18252i16 / (x0 * 3)
}

#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(g203(x0) == (-1i128))]
fn never_specfn_neg_div_eq_neg1(x0: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(g203(x0) == (-1i128))]
fn never_specfn_neg_div_eq_neg1_proof(x0: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(q203(x0) == 1)]
fn never_specfn_div_eq_1(x0: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures((-(18252i16 / (x0 * 3))) == (-1i128))]
fn never_inline_neg_div_eq_neg1(x0: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures((18252i16 / (x0 * 3)) == 1)]
fn never_inline_div_eq_1(x0: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(y == 39050)]
#[trust_vc::ensures((18252i16 / y) == 1)]
fn never_inline_div_pinned_eq_1(y: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(y == 39050)]
#[trust_vc::ensures((18252i16 / y) == -1)]
fn never_inline_div_pinned_eq_neg1(y: u16) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(g203(x0) == 0)]
fn control_specfn_neg_div_eq_0(x0: u16) {}

#[trust_vc::spec]
fn inc8(x: u8) -> u8 {
    x + 1
}

#[trust_vc::spec]
fn inc8_eq7(x: u8) -> bool {
    x + 1 == 7
}

#[trust_vc::spec]
fn dbl_mixed(x: u8, y: i16) -> int {
    (x * 2) + y
}

#[trust_vc::spec]
fn div_mixed(x: u16) -> int {
    18252i16 / x
}

#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(inc8(x) == 7)]
fn never_exec_specfn_overflowing_body_same_type(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(inc8(x) == 7)]
fn never_proof_specfn_overflowing_body_same_type(x: u8) {}

#[trust_vc::requires(x == 255)]
#[trust_vc::ensures(inc8_eq7(x))]
fn never_exec_specfn_bool_overflowing_body(x: u8) {}

#[trust_vc::requires(x == 200)]
#[trust_vc::requires(y == 0)]
#[trust_vc::ensures(dbl_mixed(x, y) == 7)]
fn never_exec_specfn_overflowing_body_mixed(x: u8, y: i16) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 200)]
#[trust_vc::requires(y == 0)]
#[trust_vc::ensures(dbl_mixed(x, y) == 7)]
fn never_proof_specfn_overflowing_body_mixed(x: u8, y: i16) {}

#[trust_vc::requires(x == 39050)]
#[trust_vc::ensures(div_mixed(x) == -1)]
fn never_exec_specfn_mixed_div_no_overflow(x: u16) {}

#[trust_vc::requires(x == 255)]
fn never_exec_assert_specfn_overflowing_body(x: u8) {
    trust_vc::assert!(inc8(x) == 7);
}

#[trust_vc::spec]
fn p114(x0: u64, x1: i32, x2: u128, x3: i8) -> bool {
    (((x1 - (-2147483648)) * (x0 + 71i8)) + (x2 << 22u32)) > x3
}

#[trust_vc::requires(x0 == 256)]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::requires(x2 == 100)]
#[trust_vc::requires(x3 == 0)]
#[trust_vc::ensures(p114(x0, x1, x2, x3))]
fn same_a_specfn_i32_wrap(x0: u64, x1: i32, x2: u128, x3: i8) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 256)]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::requires(x2 == 100)]
#[trust_vc::requires(x3 == 0)]
#[trust_vc::ensures((((x1 - (-2147483648)) * (x0 + 71i8)) + (x2 << 22u32)) > x3)]
fn same_a_inline_i32_wrap(x0: u64, x1: i32, x2: u128, x3: i8) {}

#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(g203(x0) == 5)]
fn never_exec_specfn_neg_div_eq_5(x0: u16) {}

#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(g203(x0) == 0 && g203(x0) == -1)]
fn never_exec_specfn_neg_div_contradiction(x0: u16) {}

#[trust_vc::requires(x0 == 34862)]
#[trust_vc::ensures(q203(x0) == 7)]
fn never_exec_specfn_div_eq_7(x0: u16) {}

#[trust_vc::requires(x0 == 256)]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::requires(x2 == 100)]
#[trust_vc::requires(x3 == 0)]
#[trust_vc::ensures(p114(x0, x1, x2, x3) && !p114(x0, x1, x2, x3))]
fn never_exec_specfn_p114_contradiction(x0: u64, x1: i32, x2: u128, x3: i8) {}

#[trust_vc::requires(x1 == 3)]
#[trust_vc::ensures(s114(x1) == 12345)]
fn never_exec_specfn_i32_sub_eq_12345(x1: i32) {}

#[trust_vc::spec]
fn v1(x: u16) -> int {
    5i16 / (x * 3)
}

#[trust_vc::spec]
fn v3(x: u16) -> int {
    5i16 + (x * 3)
}

#[trust_vc::spec]
fn v4(x: u16) -> u16 {
    x * 3
}

#[trust_vc::spec]
fn v5(x: i32) -> int {
    (x - (-2147483648)) * 2i64
}

#[trust_vc::spec]
fn v6(x: i32) -> int {
    (x - (-2147483648)) + 2i64
}

#[trust_vc::spec]
fn v7(x: i32) -> int {
    (x + 2147483647) * 2i64
}

#[trust_vc::spec]
fn v9(x: u16) -> int {
    (x * 3u16) + 5i16
}

#[trust_vc::requires(x == 34862)]
#[trust_vc::ensures(v1(x) == 0 && v1(x) == 1)]
fn never_vac_mixed_div_overflowing_divisor(x: u16) {}

#[trust_vc::requires(x == 2)]
#[trust_vc::ensures(v1(x) == 0 && v1(x) == 1)]
fn never_vac_mixed_div_no_overflow(x: u16) {}

#[trust_vc::requires(x == 34862)]
#[trust_vc::ensures(v3(x) == 0 && v3(x) == 1)]
fn never_vac_mixed_add_overflowing_operand(x: u16) {}

#[trust_vc::requires(x == 34862)]
#[trust_vc::ensures(v4(x) == 0 && v4(x) == 1)]
fn never_vac_same_type_overflow(x: u16) {}

#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v5(x) == 0 && v5(x) == 1)]
fn never_vac_i32_sub_neg_literal_mul_i64(x: i32) {}

#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v6(x) == 0 && v6(x) == 1)]
fn never_vac_i32_sub_neg_literal_add_i64(x: i32) {}

#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v7(x) == 0 && v7(x) == 1)]
fn never_vac_i32_add_max_mul_i64(x: i32) {}

#[trust_vc::requires(x == 34862)]
#[trust_vc::ensures(v9(x) == 0 && v9(x) == 1)]
fn never_vac_typed_u16_mul_add_i16(x: u16) {}

#[trust_vc::requires(x == 34862)]
fn never_vac_exec_assert(x: u16) {
    trust_vc::assert!(v1(x) == 0 && v1(x) == 1);
}

#[trust_vc::spec]
fn v8(x: i64) -> int {
    (x + 9223372036854775807) * 2i128
}

#[trust_vc::spec]
fn v10(x: u8) -> int {
    (x + 255) * 2u16
}

#[trust_vc::requires(x >= 3)]
#[trust_vc::requires(x <= 3)]
#[trust_vc::ensures(v7(x) == 0 && v7(x) == 1)]
fn never_vac_i32_add_max_mul_i64_range_pin(x: i32) {}

#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v8(x) == 0 && v8(x) == 1)]
fn never_vac_i64_add_max_mul_i128(x: i64) {}

#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v10(x) == 0 && v10(x) == 1)]
fn never_vac_u8_add_mul_u16(x: u8) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v7(x) == 0 && v7(x) == 1)]
fn never_vac_i32_add_max_mul_i64_proof(x: i32) {}

#[trust_vc::proof]
#[trust_vc::ensures(v7(x) == 0 && v7(x) == 1)]
fn never_vac_v7_unconstrained(x: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(x > 0)]
#[trust_vc::requires(x < 10)]
#[trust_vc::ensures(v7(x) != v7(x))]
fn never_vac_v7_ne_itself(x: i32) {}

#[trust_vc::proof]
#[trust_vc::ensures(v7(3i32) == 0 && v7(3i32) == 1)]
fn never_vac_v7_literal_arg() {}

#[trust_vc::proof]
#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v7(x) == -4294967292)]
fn excl_v7_wraps_in_i32(x: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(x == 3)]
#[trust_vc::ensures(v7(x) == 4294967300)]
fn excl_v7_exact(x: i32) {}

#[trust_vc::spec]
fn w1(x: i32) -> int {
    (x + 1) * 2i64
}

#[trust_vc::spec]
fn w4(x: i32, y: i64) -> int {
    (x + 1) + y
}

#[trust_vc::spec]
fn w6(x: u32) -> int {
    (x + 1) * 2u64
}

#[trust_vc::spec]
fn w7(x: i32) -> i32 {
    (x + 1) * 2
}

#[trust_vc::spec]
fn w8(x: i32) -> bool {
    (x + 1) * 2i64 > 0
}

#[trust_vc::proof]
#[trust_vc::ensures(w1(x) == 0 && w1(x) == 1)]
fn never_axiom_i32_plus_1_times_i64(x: i32) {}

#[trust_vc::proof]
#[trust_vc::ensures(w4(x, y) == 0 && w4(x, y) == 1)]
fn never_axiom_i32_plus_1_plus_i64(x: i32, y: i64) {}

#[trust_vc::proof]
#[trust_vc::ensures(w6(x) == 0 && w6(x) == 1)]
fn never_axiom_u32_plus_1_times_u64(x: u32) {}

#[trust_vc::proof]
#[trust_vc::ensures(w7(x) == 0 && w7(x) == 1)]
fn never_axiom_i32_same_type(x: i32) {}

#[trust_vc::proof]
#[trust_vc::ensures(w8(x) && !w8(x))]
fn never_axiom_i32_bool_body(x: i32) {}

#[trust_vc::proof]
#[trust_vc::ensures(false)]
fn never_axiom_false_after_mention(x: i32) {
    trust_vc::assert!(w1(x) == w1(x));
}

#[trust_vc::requires(x == 5)]
#[trust_vc::ensures(w1(x) == 7)]
fn never_axiom_exec_w1_eq_7(x: i32) {}

#[trust_vc::spec]
fn d1(x: u16) -> int {
    5i16 / x
}

#[trust_vc::spec]
fn d2(x: u16, y: u16) -> int {
    5i16 / (x * y)
}

#[trust_vc::spec]
fn d3(x: u16) -> int {
    5i16 % (x * 3)
}

#[trust_vc::proof]
#[trust_vc::ensures(v1(x) == 0 && v1(x) == 1)]
fn never_axiom_mixed_div_wrapping_divisor(x: u16) {}

#[trust_vc::proof]
#[trust_vc::ensures(d1(x) == 0 && d1(x) == 1)]
fn never_axiom_mixed_div_plain(x: u16) {}

#[trust_vc::proof]
#[trust_vc::ensures(d2(x, y) == 0 && d2(x, y) == 1)]
fn never_axiom_mixed_div_product_divisor(x: u16, y: u16) {}

#[trust_vc::proof]
#[trust_vc::ensures(d3(x) == 0 && d3(x) == 1)]
fn never_axiom_mixed_rem_wrapping_divisor(x: u16) {}

#[trust_vc::spec]
fn s114(x1: i32) -> i32 {
    x1 - (-2147483648)
}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::ensures(s114(x1) == -2147483645)]
fn same_b_specfn_i32_sub(x1: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::ensures((x1 - (-2147483648)) == -2147483645)]
fn same_b_inline_i32_sub(x1: i32) {}

#[trust_vc::spec]
fn t114(x0: u64, x1: i32) -> int {
    (x1 - (-2147483648)) * (x0 + 71i8)
}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 256)]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::ensures(t114(x0, x1) < 0)]
fn same_c_specfn_mixed(x0: u64, x1: i32) {}

#[trust_vc::proof]
#[trust_vc::requires(x0 == 256)]
#[trust_vc::requires(x1 == 3)]
#[trust_vc::ensures((((x1 as int) - (-2147483648)) * ((x0 as int) + 71)) < 0)]
fn same_c_inline_mixed(x0: u64, x1: i32) {}
"####;

fn run(func: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/integer_typing_src");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("specfn_axioms.rs");
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(SRC.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

fn got(r: &VerifyResult) -> &'static str {
    match r {
        VerifyResult::Verified => "Verified",
        VerifyResult::Counterexample { .. } => "Refuted",
        VerifyResult::NotProved { .. } => "NotProved",
        _ => "Unknown",
    }
}

#[test]
fn spec_fn_definitions_stay_consistent() {
    let names: Vec<&str> = SRC
        .lines()
        .filter_map(|l| l.strip_prefix("fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| {
            n.starts_with("never_")
                || n.starts_with("control_")
                || n.starts_with("same_")
                || n.starts_with("excl_")
        })
        .collect();
    let mut bad = Vec::new();
    let mut verdicts = std::collections::BTreeMap::new();
    let mut exclusive = std::collections::BTreeMap::new();
    for func in names {
        let r = run(func);
        let g = got(&r);
        let raw: String = format!("{r:?}").chars().take(200).collect();
        println!("SPECFN|{func}|{g}|{raw}");
        if func.starts_with("never_") && g == "Verified" {
            bad.push(format!("FALSE VERIFIED {func}"));
        }
        if func.starts_with("control_") && g == "Refuted" {
            bad.push(format!("FALSE COUNTEREXAMPLE {func}"));
        }
        if let Some(rest) = func.strip_prefix("excl_") {
            let key = rest.split('_').next().unwrap_or("").to_string();
            exclusive
                .entry(key)
                .or_insert_with(Vec::new)
                .push((func, g));
        }
        if let Some(rest) = func.strip_prefix("same_") {
            let key = rest.split('_').next().unwrap_or("").to_string();
            verdicts.entry(key).or_insert_with(Vec::new).push((func, g));
        }
    }
    for (key, vs) in &verdicts {
        let decided: Vec<_> = vs
            .iter()
            .filter(|(_, g)| *g == "Verified" || *g == "Refuted")
            .collect();
        if decided.len() == 2 && decided[0].1 != decided[1].1 {
            bad.push(format!("INCONSISTENT same_{key}: {decided:?}"));
        }
    }
    for (key, vs) in &exclusive {
        if vs.len() == 2 && vs.iter().all(|(_, g)| *g == "Verified") {
            bad.push(format!("BOTH VERIFIED excl_{key}: {vs:?}"));
        }
    }
    println!("SUMMARY {bad:?}");
    assert!(bad.is_empty(), "{bad:#?}");
}
