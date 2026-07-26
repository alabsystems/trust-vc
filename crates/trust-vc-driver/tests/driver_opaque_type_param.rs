// Opaque type-parameter sort (Slice 3c): bespoke expected-verdict tests +
// monomorphized cross-check.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// There is NO driver-vs-syn oracle for the opaque type-param sort: syn cannot
// resolve `ty::Param`, which is exactly why the rustc driver wins here. So this
// file builds TWO independent, self-contained checks (never a driver==syn diff on
// the SAME generic source):
//
//   (A) BESPOKE EXPECTED-VERDICT tests. The verdict of each generic function is
//       known BY CONSTRUCTION: a for-all-T tautology VERIFIES; a for-all-T false
//       claim is REFUTED (the opaque sort admits >=2 elements — no singleton
//       collapse, pinned directly by `opaque_type_param_probe.rs`); a
//       structure-assuming use of a `T` value (ordering, a trait-method call, an
//       unmodeled tuple position) FAILS CLOSED. The driver compiles the generic
//       source with real rustc, walks THIR over the opaque sort, and must land on
//       exactly those verdicts.
//
//   (B) MONOMORPHIZED CROSS-CHECK (a necessary-condition oracle). Each VERIFY/
//       REFUTE case is mirrored at a concrete `T = u32` through the trusted syn
//       `VerificationContext` path; the driver's for-all-T verdict must MATCH.
//       If the driver ever said Verified-for-all-T where syn says Refuted-at-u32,
//       the generic verdict would be unsound — the cross-check catches that.
//
// SPEC EQUALITY. Rust `==`/`!=` on a generic `T` desugar to `PartialEq` TRAIT
// method calls, which fail closed (an arbitrary `PartialEq` impl need not be the
// mathematical congruence, so treating it as `=` would be unsound). Mathematical
// (spec) equality IS a congruence for every concrete `T`, so it is carried by the
// dedicated `spec_eq`/`spec_ne` markers (recognized by bare `item_name`), lowered
// to a raw solver `=`/`!=` over the opaque sort — sound for all `T`.
//
// BOUNDARY. Datatype CONSTRUCTION with an opaque field (`S { f: x }`, `Opt::Some(x)`)
// FAILS CLOSED: it emits a `var == constructor` datatype assumption that trips a
// panic in ay's datatype `check_sat_assuming` path over the uninterpreted sort
// (caught → Unknown). Not touching ay, the driver refuses it rather than emit an
// Unknown-inducing encoding. Field PROJECTION + EUF equality over the opaque sort
// (the rest of Slice 3c) is unaffected and fully supported here.
//
// Feature-gated: empty on the default (stable) build. Run via
// `scripts/build-trust-vc-driver.sh test`.
#![cfg(feature = "rustc-driver")]
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use trust_vc_driver::driver::{self, DriverError, DriverResult};
use trust_vc_driver::lower::{outcome_from, Outcome};

use trust_vc_core::ir::{DatatypeVariant, TrustVcType};
use trust_vc_core::vc::{ProofObligation, VerificationContext};

/// Generic source compiled by the driver. Local marker shims (`requires`,
/// `ensures`) plus the SPEC-EQUALITY markers (`spec_eq`/`spec_ne`, by-reference so
/// a non-`Copy` `T` need not be moved to compare it). Generic datatypes carry
/// `T`-typed fields (the opaque sort). Every generic function is `T: Copy` ONLY so
/// the by-value spec surface borrow-checks under vanilla rustc; the driver treats
/// `T` as fully opaque and never uses `Copy` in its reasoning (a value is read as
/// a functional selector application, sound for the spec field of ANY `T`).
const SOURCE: &str = r#"
fn requires(_b: bool) {}
fn ensures(_b: bool) {}
fn spec_eq<T>(_a: &T, _b: &T) -> bool { true }
fn spec_ne<T>(_a: &T, _b: &T) -> bool { true }

struct S<T> { f: T, g: T }
struct P<A, B> { a: A, b: B }
enum Opt<T> { None, Some(T) }

// (1) identity pass-through: result == x holds for all T → Verified.
fn id_verify<T: Copy>(x: T) -> T {
    let result = x;
    ensures(spec_eq(&result, &x));
    result
}

// (2) spec_ne on equal values: result != x is FALSE (result == x) → Refuted.
fn ne_refute<T: Copy>(x: T) -> T {
    let result = x;
    ensures(spec_ne(&result, &x));
    result
}

// (3) projection identity: result == s.f holds for all T → Verified.
fn proj_identity_verify<T: Copy>(s: S<T>) -> T {
    let result = s.f;
    ensures(spec_eq(&result, &s.f));
    result
}

// (4) reading a DIFFERENT field: result(==s.f) == s.g is not forced (distinct
//     selectors over an opaque sort with >=2 elements) → Refuted.
fn proj_wrong_field_refute<T: Copy>(s: S<T>) -> T {
    let result = s.f;
    ensures(spec_eq(&result, &s.g));
    result
}

// (5) TWO type parameters (distinct params A, B; distinct fields a: A, b: B):
//     projection identity p.a == p.a for all A, B → Verified.
fn two_param_proj_verify<A: Copy, B: Copy>(p: P<A, B>) -> A {
    let result = p.a;
    ensures(spec_eq(&result, &p.a));
    result
}

// (6) T-ORDERING use: `s.f < s.g` is a PartialOrd trait call — no total order
//     exists on an arbitrary T — so it FAILS CLOSED (never Verified/Refuted).
fn ord_use_fail_closed<T: Copy + PartialOrd>(s: S<T>) -> bool {
    let result = true;
    ensures(s.f < s.g);
    result
}

// (7) STRUCT construction with an opaque field → VERIFIES (construct-then-
//     project roundtrip result == x holds for all T; selector-of-constructor is
//     a datatype axiom, sound over the uninterpreted sort).
fn construct_struct_verify<T: Copy>(x: T, y: T) -> T {
    let s = S { f: x, g: y };
    let result = s.f;
    ensures(spec_eq(&result, &x));
    result
}

// (8) generic ENUM construction with an opaque payload → VERIFIES (Some(x) then
//     match payload == x holds for all T; constructor/selector datatype axioms).
fn construct_enum_verify<T: Copy>(x: T) -> T {
    let o = Opt::Some(x);
    let result = match o { Opt::None => x, Opt::Some(v) => v };
    ensures(spec_eq(&result, &x));
    result
}

// (9) a type parameter in an UNMODELED position (a tuple `(T, T)` param):
//     `map_opaque_type_param` does not model tuples → FAILS CLOSED.
fn tuple_param_fail_closed<T: Copy>(t: (T, T)) -> bool {
    let _first = t.0;
    let result = true;
    ensures(result);
    result
}
"#;

fn u32t() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

/// Compiles `SOURCE` through the rustc driver and returns the collected results.
fn run_driver() -> Vec<DriverResult> {
    let dir = std::env::temp_dir().join(format!("trust_vc_opaque_tp_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("opaque_src.rs");
    std::fs::write(&path, SOURCE).expect("write source");

    let sysroot = {
        let out = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .expect("run rustc --print sysroot");
        String::from_utf8(out.stdout)
            .expect("utf8 sysroot")
            .trim()
            .to_string()
    };

    let args = vec![
        "trust-vc-driver".to_string(),
        path.to_string_lossy().into_owned(),
        "--edition=2021".to_string(),
        "--crate-type=lib".to_string(),
        "--crate-name=opaque".to_string(),
        "--emit=metadata".to_string(),
        format!("--out-dir={}", dir.display()),
        "--sysroot".to_string(),
        sysroot,
        "-Awarnings".to_string(),
    ];
    driver::run(&args)
}

fn find<'a>(results: &'a [DriverResult], name: &str) -> &'a Result<Outcome, DriverError> {
    &results
        .iter()
        .find(|r| r.function == name)
        .unwrap_or_else(|| panic!("driver produced no result for `{name}`: {results:?}"))
        .result
}

fn is_fail_closed(r: &Result<Outcome, DriverError>) -> bool {
    matches!(
        r,
        Err(DriverError::UnsupportedContract(_)) | Err(DriverError::UnsupportedType(_))
    )
}

// --- syn concrete (T = u32) mirrors: the trusted necessary-condition oracle. ---

/// `S { f: u32, g: u32 }` — the concrete monomorphization of `S<T>` at `u32`.
fn s_u32_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "S".to_string(),
        variants: vec![DatatypeVariant::new(
            "S",
            vec![("f".to_string(), u32t()), ("g".to_string(), u32t())],
        )],
    }
}

/// `P { a: u32, b: u32 }` — `P<u32, u32>`.
fn p_u32_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "P".to_string(),
        variants: vec![DatatypeVariant::new(
            "P",
            vec![("a".to_string(), u32t()), ("b".to_string(), u32t())],
        )],
    }
}

/// Run a syn `VerificationContext` at `T = u32` (declared vars + assume strings +
/// a single assert string), under the same exec overflow semantics the driver
/// uses. This is the concrete monomorphic mirror the driver's for-all-T verdict
/// is cross-checked against.
fn syn_u32_outcome(
    vars: &[(&str, TrustVcType)],
    assumes: &[(&str, &str)],
    assert_cond: &str,
) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    for (name, ty) in vars {
        ctx.declare_var_typed(*name, ty.clone());
    }
    for (name, cond) in assumes {
        ctx.push_obligation(ProofObligation::assume(*name, *cond));
    }
    ctx.push_obligation(ProofObligation::assert("ensures_0", assert_cond));
    outcome_from(&ctx.verify())
}

#[test]
fn opaque_type_param_bespoke_verdicts_and_mono_crosscheck() {
    let results = run_driver();

    // ---------- (A) bespoke expected verdicts ----------
    let id = find(&results, "id_verify");
    assert_eq!(id, &Ok(Outcome::Verified), "id_verify");

    let ne = find(&results, "ne_refute");
    assert_eq!(ne, &Ok(Outcome::Refuted), "ne_refute");

    let proj_v = find(&results, "proj_identity_verify");
    assert_eq!(proj_v, &Ok(Outcome::Verified), "proj_identity_verify");

    let proj_r = find(&results, "proj_wrong_field_refute");
    assert_eq!(proj_r, &Ok(Outcome::Refuted), "proj_wrong_field_refute");

    let two = find(&results, "two_param_proj_verify");
    assert_eq!(two, &Ok(Outcome::Verified), "two_param_proj_verify");

    // T-ordering must FAIL CLOSED — never a fabricated Verified/Refuted.
    let ord = find(&results, "ord_use_fail_closed");
    assert!(
        matches!(ord, Err(DriverError::UnsupportedContract(_))),
        "ord_use_fail_closed must fail closed, got {ord:?}"
    );

    // Opaque-field STRUCT / ENUM construction now VERIFIES (construct-then-project
    // roundtrip result == x holds for all T; selector-of-constructor datatype
    // axiom, sound over the uninterpreted sort — ay drain-fix + main's DT-value
    // congruence). The encoder probe (opaque_type_param_probe.rs) independently
    // pins the datatype roundtrip + no-singleton-collapse soundness.
    let cs = find(&results, "construct_struct_verify");
    assert_eq!(
        cs,
        &Ok(Outcome::Verified),
        "construct_struct_verify (roundtrip result==x for all T)"
    );
    let ce = find(&results, "construct_enum_verify");
    assert_eq!(
        ce,
        &Ok(Outcome::Verified),
        "construct_enum_verify (Some(x) match payload==x for all T)"
    );

    // Type param in an unmodeled position (tuple) fails closed.
    let tup = find(&results, "tuple_param_fail_closed");
    assert!(
        is_fail_closed(tup),
        "tuple_param_fail_closed must fail closed, got {tup:?}"
    );

    // ---------- (B) monomorphized cross-check at T = u32 ----------
    // Each concrete mirror must AGREE with the driver's for-all-T verdict above;
    // in particular no driver-Verified may correspond to a syn-Refuted-at-u32.
    let uv = || u32t();

    let syn_id = syn_u32_outcome(
        &[("x", uv()), ("result", uv())],
        &[("body", "result == x")],
        "result == x",
    );
    assert_eq!(syn_id, Outcome::Verified, "syn u32: id");
    assert_eq!(id, &Ok(syn_id), "id_verify: driver for-all-T == syn u32");

    let syn_ne = syn_u32_outcome(
        &[("x", uv()), ("result", uv())],
        &[("body", "result == x")],
        "result != x",
    );
    assert_eq!(syn_ne, Outcome::Refuted, "syn u32: ne");
    assert_eq!(ne, &Ok(syn_ne), "ne_refute: driver == syn u32");

    let syn_proj_v = syn_u32_outcome(
        &[("s", s_u32_ty()), ("result", uv())],
        &[("body", "result == s.f")],
        "result == s.f",
    );
    assert_eq!(syn_proj_v, Outcome::Verified, "syn u32: proj identity");
    assert_eq!(proj_v, &Ok(syn_proj_v), "proj_identity: driver == syn u32");

    let syn_proj_r = syn_u32_outcome(
        &[("s", s_u32_ty()), ("result", uv())],
        &[("body", "result == s.f")],
        "result == s.g",
    );
    assert_eq!(syn_proj_r, Outcome::Refuted, "syn u32: proj wrong field");
    assert_eq!(
        proj_r,
        &Ok(syn_proj_r),
        "proj_wrong_field: driver == syn u32"
    );

    let syn_two = syn_u32_outcome(
        &[("p", p_u32_ty()), ("result", uv())],
        &[("body", "result == p.a")],
        "result == p.a",
    );
    assert_eq!(syn_two, Outcome::Verified, "syn u32: two-param projection");
    assert_eq!(
        two,
        &Ok(syn_two),
        "two_param_proj_verify: driver == syn u32"
    );
}
