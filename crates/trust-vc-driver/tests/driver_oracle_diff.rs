// Driver-vs-syn oracle-diff: the soundness gate for Slice 0.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// This is the soundness gate for the rustc-driver THIR front end (Slice 0 of
// the internal Verus-replacement plan). For minimal scalar-Hoare functions it runs
// the SAME contract through two independent front ends and asserts the verdicts
// AGREE:
//
//   * driver path  — `driver::run` compiles the source with rustc, walks the
//     fully type-checked THIR, lowers the scalar Hoare fragment into a
//     `DriverFn`, and verifies it through the real encoder + ay.
//   * syn path      — the established string-condition path: a
//     `VerificationContext` built from the equivalent requires / body-relation /
//     ensures strings (parsed and lowered by the syn lowerer), verified through
//     the same encoder + ay.
//
// Both run under exec arithmetic semantics (overflow / div0 / shift checks on),
// so the comparison is apples-to-apples. The driver is a NEW VC producer; this
// diff is what proves the THIR path agrees with the trusted syn path rather than
// silently proving more (or less) than the program.
//
// Cases:
//   (a) a true postcondition VERIFIES on both,
//   (b) a false postcondition is REFUTED on both,
//   (c) an out-of-fragment construct (a loop) returns UnsupportedContract —
//       fail-closed, never a fabricated verdict.
//
// Feature-gated: this whole file is empty in the default (no-feature) build.
// Run via `targo --unverified test -p trust-vc-driver --features rustc-driver`.
#![cfg(feature = "rustc-driver")]
// Linking the feature-on `trust-vc-driver` lib pulls in `rustc_driver`, which the
// linking crate (this test binary) must opt into; build.rs bakes the rpath to
// the compiler's lib dir so the dynamic compiler libs resolve.
#![cfg_attr(feature = "rustc-driver", feature(rustc_private))]

use trust_vc_driver::driver::{self, DriverError, DriverResult};
use trust_vc_driver::lower::{outcome_from, Outcome};

use trust_vc_core::ir::{DatatypeVariant, TrustVcType};
use trust_vc_core::vc::{ProofObligation, TypedProofObligation, VerificationContext};
use trust_vc_core::{ir::TrustVcExpr, ir_builder};

/// Source compiled by the driver. Three scalar-Hoare functions plus the two
/// no-op marker shims (`requires`/`ensures`) that make the contract surface
/// type-check under vanilla rustc. Only the three contract-bearing functions are
/// verification targets; the marker shims carry no `ensures`, so the driver
/// skips them.
const SOURCE: &str = r#"
fn requires(_b: bool) {}
fn ensures(_b: bool) {}

fn verify_case(x: u32) -> u32 {
    requires(x < 100);
    let result = x + 1;
    ensures(result == x + 1);
    result
}

fn refute_case(x: u32) -> u32 {
    requires(x < 100);
    let result = x + 1;
    ensures(result == x + 2);
    result
}

fn out_of_fragment_case(n: u32) -> u32 {
    requires(n < 100);
    let mut total = 0u32;
    while total < n {
        total = total + 1;
    }
    let result = total;
    ensures(result <= n);
    result
}

// --- Slice 2: scalar quantifiers ---------------------------------------------
// The spec math-integer `int` plus the `forall`/`exists` marker shims, defined so
// vanilla rustc type-checks the quantifier surface (mirroring the requires/ensures
// shims). The `int` operators are overloaded so the body type-checks; the driver
// reinterprets them as UNBOUNDED math arithmetic (spec semantics), so `x < x + 1`
// holds for all `x` (no overflow), exactly as the syn `ir_builder::forall` does.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
#[allow(non_camel_case_types)]
struct int(i128);
impl core::ops::Add<i128> for int {
    type Output = int;
    fn add(self, rhs: i128) -> int { int(self.0.wrapping_add(rhs)) }
}

fn forall<F: Fn(int) -> bool>(_f: F) -> bool { true }
fn exists<F: Fn(int) -> bool>(_f: F) -> bool { true }
fn unknown_pred(_x: int) -> bool { true }

// (a) LINEAR true postcondition: forall x:int. x < x + 1  → Verified on both.
fn forall_lt_succ() -> bool {
    let result = true;
    ensures(forall(|x: int| x < x + 1));
    result
}

// (b) false postcondition: forall x:int. x < x  → Refuted on both.
fn forall_lt_self() -> bool {
    let result = true;
    ensures(forall(|x: int| x < x));
    result
}

// existential: exists x:int. x < x + 1  → Verified on both (every x is a witness).
fn exists_lt_succ() -> bool {
    let result = true;
    ensures(exists(|x: int| x < x + 1));
    result
}

// (c1) untyped/inferred binder → fail closed (NOT a fabricated verdict).
fn forall_untyped() -> bool {
    let result = true;
    ensures(forall(|x| x < x + 1));
    result
}

// (c2) out-of-fragment closure BODY (a general call) → fail closed.
fn forall_oof_body() -> bool {
    let result = true;
    ensures(forall(|x: int| unknown_pred(x)));
    result
}

// --- Block-wrapped quantifiers (the `forall!`/`exists!` macro surface shape) --
// Under `--cfg trust_vc_driver` the contract macros expand a quantifier to a
// BLOCK that binds a pure typecheck-aid closure then yields the real marker call:
// `{ let _c = |x: int| ..; { forall(|x: int| ..) } }` (see
// `trust-vc/src/macro_expand_ext.rs::expand_forall`). These functions hand-write
// exactly that shape so the driver must PEEL the pure wrapper and lower the REAL
// quantifier (Slice 2) — reaching the same verdict as the direct (unwrapped)
// `forall` reference, proving it lowered the real quantifier, NOT a vacuous
// constant, and NOT the ignored `let`-bound typecheck closure.

// (a) TRUE block-wrapped forall postcondition → Verified on both.
fn forall_block_verify() -> bool {
    let result = true;
    ensures({ let _c = |x: int| x < x + 1; { forall(|x: int| x < x + 1) } });
    result
}

// (b) FALSE block-wrapped forall → Refuted on both. Proves the REAL quantifier
// was lowered THROUGH the block, not vacuously verified as a constant `true`.
fn forall_block_refute() -> bool {
    let result = true;
    ensures({ let _c = |x: int| x < x; { forall(|x: int| x < x) } });
    result
}

// exists block-wrapped: Verified on both (every x is a witness).
fn exists_block_verify() -> bool {
    let result = true;
    ensures({ let _c = |x: int| x < x + 1; { exists(|x: int| x < x + 1) } });
    result
}

// (c) a block with a SIDE-EFFECTING statement BEFORE the marker → fail closed.
// The `let _z = unknown_pred(int(0));` initializer is a CALL (a non-closure
// literal that could have effects), so the whitelist refuses the whole block —
// never assuming block == tail when a statement could have effects.
fn forall_block_side_effect_oof() -> bool {
    let result = true;
    ensures({ let _z = unknown_pred(int(0)); { forall(|x: int| x < x + 1) } });
    result
}

// --- Slice 3a: scalar structs ------------------------------------------------
// A NON-RECURSIVE, NON-GENERIC, NAMED-FIELD struct whose fields are all scalar
// (`u32`). The driver maps it to a single-variant datatype, lowering field
// projection `p.x` to the encoder SELECTOR and construction `Point { .. }` to the
// CONSTRUCTOR — the exact shape the syn front end produces — so a TRUE field
// postcondition Verifies, a FALSE one is Refuted, and the per-field constraints
// are never dropped (a dropped `p.x < 100` would let (b) wrongly verify).
struct Point { x: u32, y: u32 }

// (a) TRUE postcondition over a struct field: requires p.x < 100 ⇒ result < 200.
fn struct_field_verify(p: Point) -> u32 {
    requires(p.x < 100);
    let result = p.x;
    ensures(result < 200);
    result
}

// (b) FALSE postcondition over a struct field: p.x < 100 does NOT imply p.x < 50.
fn struct_field_refute(p: Point) -> u32 {
    requires(p.x < 100);
    let result = p.x;
    ensures(result < 50);
    result
}

// constructed struct reads back: build Point { x: a, y: 0 }, read `.x` == a
// (exercises CONSTRUCTOR then SELECTOR through the native datatype roundtrip).
fn struct_construct_roundtrip(a: u32) -> u32 {
    requires(a < 100);
    let p = Point { x: a, y: 0 };
    let result = p.x;
    ensures(result == a);
    result
}

// (c1) out-of-fragment SCALAR match (scrutinee is a `u32`, not an enum, and has a
// wildcard/literal arm) → still fails closed under Slice 3b (only ENUM scrutinees
// with one bare-variant arm per variant are in the match fragment).
fn struct_match_oof(x: u32) -> u32 {
    requires(x < 10);
    let result = match x { 0 => 0u32, _ => 1u32 };
    ensures(result <= 1);
    result
}

// Slice 3b promotes a scalar `enum` value into the fragment: constructing the unit
// variant `Choice::First` now lowers to the datatype CONSTRUCTOR, so this verifies
// (the enum binding is unused; `result < 10` follows from `x < 10`).
enum Choice { First, Second }
fn struct_enum_oof(x: u32) -> u32 {
    requires(x < 10);
    let _c = Choice::First;
    let result = x;
    ensures(result < 10);
    result
}

// --- Slice 3b: scalar enums + simple match -----------------------------------
// A NON-RECURSIVE, NON-GENERIC enum with a unit variant and a scalar-payload
// tuple variant. The driver maps it to a MULTI-variant datatype: construction
// `E::B(a)` lowers to the CONSTRUCTOR (variant_index = B) and
// `match e { E::A => .., E::B(v) => .. }` to the encoder datatype MATCH
// (per-variant tester + payload selector), mirroring the syn front end's
// `lower_match`. A payload read through a matched constructed value Verifies; a
// dropped/misrouted B arm would let the refute case wrongly verify — the diff
// catches it.
enum E { A, B(u32) }

// (a) construct E::B(a), match, read the B payload: result == a. TRUE on both.
fn enum_match_verify(a: u32) -> u32 {
    requires(a < 100);
    let e = E::B(a);
    let result = match e { E::A => 0u32, E::B(v) => v };
    ensures(result == a);
    result
}

// (b) same roundtrip, FALSE postcondition: E::B(a) reads v == a, which `a < 100`
// does NOT force to 0. Refuted on both — the B arm's payload read is kept and
// the arm is matched to the RIGHT variant (a swapped/dropped arm would give 0).
fn enum_match_refute(a: u32) -> u32 {
    requires(a < 100);
    let e = E::B(a);
    let result = match e { E::A => 0u32, E::B(v) => v };
    ensures(result == 0);
    result
}

// (c1) a match arm GUARD → fail closed (never a fabricated verdict).
fn enum_match_guard_oof(a: u32) -> u32 {
    requires(a < 100);
    let e = E::B(a);
    let result = match e { E::B(v) if v < 50 => v, E::B(v) => v, E::A => 0u32 };
    ensures(result == a);
    result
}

// (c2) a wildcard/default arm (not one-bare-variant-arm-per-variant) → fail closed.
fn enum_match_wildcard_oof(a: u32) -> u32 {
    requires(a < 100);
    let e = E::B(a);
    let result = match e { E::A => 0u32, _ => 9u32 };
    ensures(result <= 9);
    result
}

// --- Attribute-block peeling: the real #[trust_vc::contract]/returns shape ------
// Under `--cfg trust_vc_driver` the `#[trust_vc::contract(requires(..),
// ensures(..), returns(ret))]` macro expands the function body into an OUTER
// transparent wrapper block whose sole content is an INNER contract block
// `{ requires(..); let ret = '__trust_vc_contract_return: { <body> }; ensures(..); ret }`
// (the `returns(..)` pass adds the outer wrapper; the `let ret` initializer is a
// LABELED block — the label carries early returns as breaks). These functions
// hand-write EXACTLY that shape so the driver must (1) PEEL the outer transparent
// wrapper to find the markers (without it, is_target=false → 0 targets) and
// (2) PEEL the labeled-block `let` initializer to its tail value. They must reach
// the SAME verdict as the bare (unwrapped) scalar-Hoare cases, proving the peel
// lowered the real body relation, not a vacuous constant.

// (a) TRUE post through the attribute-block shape → Verified on both.
fn attr_block_verify(x: u32) -> u32 {
    {
        requires(x < 100);
        let ret = '__trust_vc_contract_return: { x + 1 };
        ensures(ret == x + 1);
        ret
    }
}

// (b) FALSE post (ensures ret == x + 2) → Refuted on both. Proves the driver
// lowered the REAL body value through the labeled block, not a vacuous `true`.
fn attr_block_refute(x: u32) -> u32 {
    {
        requires(x < 100);
        let ret = '__trust_vc_contract_return: { x + 1 };
        ensures(ret == x + 2);
        ret
    }
}

// (c1) a VALUE-BREAK carrying a value out of the labeled block → fail closed.
// The block value comes from `break '__trust_vc_contract_return (x + 5)`, which
// could differ from any lowered tail; the strict whitelist rejects ExprKind::Break
// so the WHOLE contract refuses — never assuming block == tail on a value-break.
fn attr_block_value_break_oof(x: u32) -> u32 {
    {
        requires(x < 100);
        let ret = '__trust_vc_contract_return: { break '__trust_vc_contract_return x + 5 };
        ensures(ret == x + 1);
        ret
    }
}

// (c2) an EXTRA/side-effecting statement inside the labeled block → fail closed.
// The value-block peel requires EMPTY statements (a statement could carry a
// `break <value>` or a side effect), so a labeled block with a statement refuses.
fn attr_block_stmt_oof(x: u32) -> u32 {
    {
        requires(x < 100);
        let ret = '__trust_vc_contract_return: { let _w = x + 1; x + 2 };
        ensures(ret == x + 2);
        ret
    }
}
"#;

fn u32t() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

/// Reference verdict via the syn string-condition path, declaring the same two
/// scalar variables and running under the same exec overflow semantics the
/// driver uses (`verify_exec`).
fn syn_outcome(assumes: &[(&str, &str)], asserts: &[(&str, &str)]) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", u32t());
    ctx.declare_var_typed("result", u32t());
    for (name, cond) in assumes {
        ctx.push_obligation(ProofObligation::assume(*name, *cond));
    }
    for (name, cond) in asserts {
        ctx.push_obligation(ProofObligation::assert(*name, *cond));
    }
    outcome_from(&ctx.verify())
}

/// Compiles `SOURCE` through the rustc driver and returns the collected results.
fn run_driver() -> Vec<DriverResult> {
    let dir = std::env::temp_dir().join(format!("trust_vc_oracle_diff_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("oracle_src.rs");
    std::fs::write(&path, SOURCE).expect("write source");

    // The sysroot of the compiler this driver links (baked in by build.rs),
    // not whatever `rustc` PATH carries.
    let sysroot = env!("VC_DRIVER_COMPILER_SYSROOT").to_string();

    let args = vec![
        "trust-vc-driver".to_string(),
        path.to_string_lossy().into_owned(),
        "--edition=2021".to_string(),
        "--crate-type=lib".to_string(),
        "--crate-name=oracle".to_string(),
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

/// Reference verdict for a quantified postcondition via the syn front-end's own
/// builder (`ir_builder::forall`/`exists` is exactly what the `verus_code!`
/// closure-to-quantifier codegen emits), verified through the same encoder + ay
/// under the same exec overflow semantics the driver uses. This is the trusted
/// side of the oracle diff: the driver's THIR-built quantifier must reach the
/// same verdict as this hand-built reference IR.
fn syn_quant_outcome(quant: TrustVcExpr) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_typed_obligation(TypedProofObligation::assert("quant", quant));
    outcome_from(&ctx.verify())
}

fn mathint() -> TrustVcType {
    TrustVcType::MathInt
}

#[test]
fn driver_thir_agrees_with_syn_on_scalar_quantifiers() {
    let results = run_driver();

    // --- syn reference quantifiers (the trusted IR, via ir_builder) ---
    // (a) forall x:int. x < x + 1
    let x = || ir_builder::var("x", mathint());
    let ref_lt_succ = ir_builder::forall(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(
            x(),
            ir_builder::add(x(), ir_builder::int_lit(1, mathint()), mathint()),
        ),
        None,
    );
    // (b) forall x:int. x < x
    let ref_lt_self = ir_builder::forall(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(x(), x()),
        None,
    );
    // exists x:int. x < x + 1
    let ref_exists = ir_builder::exists(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(
            x(),
            ir_builder::add(x(), ir_builder::int_lit(1, mathint()), mathint()),
        ),
        None,
    );

    let syn_lt_succ = syn_quant_outcome(ref_lt_succ);
    let syn_lt_self = syn_quant_outcome(ref_lt_self);
    let syn_exists = syn_quant_outcome(ref_exists);

    // Non-degeneracy: the trusted side must land on the intended semantics, not
    // on "both Unknown". A faked-`forall` (→ true) would make (b) disagree.
    assert_eq!(syn_lt_succ, Outcome::Verified, "syn ref: forall x<x+1");
    assert_eq!(syn_lt_self, Outcome::Refuted, "syn ref: forall x<x");
    assert_eq!(syn_exists, Outcome::Verified, "syn ref: exists x<x+1");

    // (a) true quantified postcondition: driver == syn == Verified.
    let d_lt_succ = find(&results, "forall_lt_succ");
    assert_eq!(
        d_lt_succ,
        &Ok(syn_lt_succ.clone()),
        "forall_lt_succ: driver==syn"
    );
    assert_eq!(d_lt_succ, &Ok(Outcome::Verified));

    // (b) false quantified postcondition: driver == syn == Refuted.
    let d_lt_self = find(&results, "forall_lt_self");
    assert_eq!(
        d_lt_self,
        &Ok(syn_lt_self.clone()),
        "forall_lt_self: driver==syn"
    );
    assert_eq!(d_lt_self, &Ok(Outcome::Refuted));

    // existential: driver == syn == Verified.
    let d_exists = find(&results, "exists_lt_succ");
    assert_eq!(
        d_exists,
        &Ok(syn_exists.clone()),
        "exists_lt_succ: driver==syn"
    );
    assert_eq!(d_exists, &Ok(Outcome::Verified));

    // (c1) untyped/inferred binder fails closed (never a fabricated verdict).
    let d_untyped = find(&results, "forall_untyped");
    assert!(
        matches!(d_untyped, Err(DriverError::UnsupportedContract(_))),
        "forall_untyped must fail closed, got {d_untyped:?}"
    );

    // (c2) out-of-fragment closure body fails closed — the WHOLE quantifier is
    // refused, never partially synthesized to a constant.
    let d_oof = find(&results, "forall_oof_body");
    assert!(
        matches!(d_oof, Err(DriverError::UnsupportedContract(_))),
        "forall_oof_body must fail closed, got {d_oof:?}"
    );
}

/// Block-wrapped quantifiers: the SPECIFIC surface shape `forall!`/`exists!`
/// expand to under `--cfg trust_vc_driver` — `{ let _c = <closure>; { forall(..) } }`
/// (a pure typecheck-aid `let` plus a tail marker call). The driver must PEEL the
/// pure wrapper and lower the REAL quantifier, reaching the same verdict as the
/// direct (unwrapped) `ir_builder::forall`/`exists` reference. A block with a
/// side-effecting statement must FAIL CLOSED. This proves the block peel lowers
/// the real quantifier THROUGH the block, never a vacuous constant.
#[test]
fn driver_thir_agrees_with_syn_on_block_wrapped_quantifiers() {
    let results = run_driver();

    // --- syn reference quantifiers (the trusted IR, via ir_builder) ---
    let x = || ir_builder::var("x", mathint());
    // forall x:int. x < x + 1  (TRUE)
    let ref_lt_succ = ir_builder::forall(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(
            x(),
            ir_builder::add(x(), ir_builder::int_lit(1, mathint()), mathint()),
        ),
        None,
    );
    // forall x:int. x < x  (FALSE)
    let ref_lt_self = ir_builder::forall(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(x(), x()),
        None,
    );
    // exists x:int. x < x + 1  (TRUE)
    let ref_exists = ir_builder::exists(
        vec![("x".to_string(), mathint())],
        ir_builder::lt(
            x(),
            ir_builder::add(x(), ir_builder::int_lit(1, mathint()), mathint()),
        ),
        None,
    );

    let syn_lt_succ = syn_quant_outcome(ref_lt_succ);
    let syn_lt_self = syn_quant_outcome(ref_lt_self);
    let syn_exists = syn_quant_outcome(ref_exists);

    // Non-degeneracy: the trusted side lands on the intended semantics, so a
    // faked/vacuous block peel would DISAGREE (b would flip to Verified).
    assert_eq!(syn_lt_succ, Outcome::Verified, "syn ref: forall x<x+1");
    assert_eq!(syn_lt_self, Outcome::Refuted, "syn ref: forall x<x");
    assert_eq!(syn_exists, Outcome::Verified, "syn ref: exists x<x+1");

    // (a) TRUE block-wrapped forall: driver peels the pure wrapper and lowers the
    // REAL quantifier → == syn == Verified.
    let d_verify = find(&results, "forall_block_verify");
    assert_eq!(
        d_verify,
        &Ok(syn_lt_succ.clone()),
        "forall_block_verify: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_verify, &Ok(Outcome::Verified));

    // (b) FALSE block-wrapped forall: Refuted on both — PROVES the driver lowered
    // the real quantifier through the block, not a vacuous constant `true`.
    let d_refute = find(&results, "forall_block_refute");
    assert_eq!(
        d_refute,
        &Ok(syn_lt_self.clone()),
        "forall_block_refute: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_refute, &Ok(Outcome::Refuted));

    // exists block-wrapped: driver == syn == Verified.
    let d_exists = find(&results, "exists_block_verify");
    assert_eq!(
        d_exists,
        &Ok(syn_exists.clone()),
        "exists_block_verify: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_exists, &Ok(Outcome::Verified));

    // (c) a block with a SIDE-EFFECTING statement (a call before the marker)
    // fails closed. The whitelist peels ONLY pure closure-literal `let`s, so a
    // non-closure initializer refuses the WHOLE predicate — never assuming
    // block == tail when a statement could have effects.
    let d_side = find(&results, "forall_block_side_effect_oof");
    assert!(
        matches!(d_side, Err(DriverError::UnsupportedContract(_))),
        "forall_block_side_effect_oof must fail closed to UnsupportedContract, got {d_side:?}"
    );
}

/// The `Point { x: u32, y: u32 }` struct as the single-variant datatype the syn
/// front end registers for it (`StructDef::to_datatype_type`). Used to declare
/// the struct-typed reference variables on the trusted side of the diff.
fn point_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Point".to_string(),
        variants: vec![DatatypeVariant::new(
            "Point",
            vec![("x".to_string(), u32t()), ("y".to_string(), u32t())],
        )],
    }
}

/// Reference verdict for the struct-field Hoare cases via the INDEPENDENT syn
/// string-condition path: declare `p: Point` and `result: u32`, assume the
/// precondition + the `result == p.x` body relation, assert the postcondition.
/// The syn lowerer resolves `p.x` to the encoder selector on its own (it never
/// touches the driver's symbol replication), so a verdict match genuinely
/// validates the driver's THIR-built selector/constructor IR.
fn syn_struct_field_outcome(assume_cond: &str, assert_cond: &str) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("p", point_ty());
    ctx.declare_var_typed("result", u32t());
    ctx.push_obligation(ProofObligation::assume("requires_0", assume_cond));
    ctx.push_obligation(ProofObligation::assume("body", "result == p.x"));
    ctx.push_obligation(ProofObligation::assert("ensures_0", assert_cond));
    outcome_from(&ctx.verify())
}

/// Reference verdict for the construct-then-read roundtrip via the syn string
/// path: `p == Point { x: a, y: 0 }` (CONSTRUCTOR) and `result == p.x`
/// (SELECTOR), asserting `result == a`.
fn syn_struct_roundtrip_outcome(assert_cond: &str) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", u32t());
    ctx.declare_var_typed("p", point_ty());
    ctx.declare_var_typed("result", u32t());
    ctx.push_obligation(ProofObligation::assume("requires_0", "a < 100"));
    ctx.push_obligation(ProofObligation::assume(
        "body_p",
        "p == Point { x: a, y: 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume("body_r", "result == p.x"));
    ctx.push_obligation(ProofObligation::assert("ensures_0", assert_cond));
    outcome_from(&ctx.verify())
}

#[test]
fn driver_thir_agrees_with_syn_on_scalar_structs() {
    let results = run_driver();

    // --- syn reference verdicts (the trusted, independent path) ---
    let syn_verify = syn_struct_field_outcome("p.x < 100", "result < 200");
    let syn_refute = syn_struct_field_outcome("p.x < 100", "result < 50");
    let syn_roundtrip = syn_struct_roundtrip_outcome("result == a");

    // Non-degeneracy: the trusted side must land on the intended semantics, not a
    // degenerate "both Unknown". If the field constraint were dropped, (b) would
    // flip to Verified — the guard catches that.
    assert_eq!(
        syn_verify,
        Outcome::Verified,
        "syn ref: p.x<100 ⇒ result<200"
    );
    assert_eq!(syn_refute, Outcome::Refuted, "syn ref: p.x<100 ⇏ result<50");
    assert_eq!(
        syn_roundtrip,
        Outcome::Verified,
        "syn ref: (Point{{x:a,..}}).x == a"
    );

    // (a) TRUE field postcondition: driver == syn == Verified.
    let d_verify = find(&results, "struct_field_verify");
    assert_eq!(
        d_verify,
        &Ok(syn_verify.clone()),
        "struct_field_verify: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_verify, &Ok(Outcome::Verified));

    // (b) FALSE field postcondition: driver == syn == Refuted (constraint kept).
    let d_refute = find(&results, "struct_field_refute");
    assert_eq!(
        d_refute,
        &Ok(syn_refute.clone()),
        "struct_field_refute: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_refute, &Ok(Outcome::Refuted));

    // construct-then-read roundtrip: driver == syn == Verified.
    let d_roundtrip = find(&results, "struct_construct_roundtrip");
    assert_eq!(
        d_roundtrip,
        &Ok(syn_roundtrip.clone()),
        "struct_construct_roundtrip: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_roundtrip, &Ok(Outcome::Verified));

    // (c1) out-of-fragment SCALAR `match` (scrutinee is a `u32`, plus a wildcard
    // arm) still fails closed under Slice 3b — only enum scrutinees are in the
    // match fragment.
    let d_match = find(&results, "struct_match_oof");
    assert!(
        matches!(d_match, Err(DriverError::UnsupportedContract(_))),
        "struct_match_oof must fail closed to UnsupportedContract, got {d_match:?}"
    );

    // Slice 3b promoted the scalar `enum` value into the fragment: constructing
    // `Choice::First` now lowers to the datatype constructor, so this Verifies
    // (the enum binding is unused; `result < 10` follows from `x < 10`). The rich
    // enum/match semantics are cross-checked against syn in
    // `driver_thir_agrees_with_syn_on_enums_and_match`.
    let d_enum = find(&results, "struct_enum_oof");
    assert_eq!(
        d_enum,
        &Ok(Outcome::Verified),
        "struct_enum_oof: unit-variant enum construction is in the Slice 3b fragment, got {d_enum:?}"
    );
}

/// The `enum E { A, B(u32) }` as the multi-variant datatype the syn front end
/// registers for it (unit variant `A`; tuple variant `B` whose sole positional
/// field is named `"0"`, matching the builtins' scheme). Used to declare the
/// enum-typed reference variable on the trusted side of the diff — declaring it
/// registers the variant metadata, so the syn path resolves `E::B(a)`
/// construction and the `E::A` / `E::B(v)` match patterns on its own.
fn e_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "E".to_string(),
        variants: vec![
            DatatypeVariant::new("A", vec![]),
            DatatypeVariant::new("B", vec![("0".to_string(), u32t())]),
        ],
    }
}

/// Reference verdict for the enum construct-then-match roundtrip via the
/// INDEPENDENT syn string-condition path: declare `a: u32`, `e: E`, `result: u32`;
/// assume `a < 100`, the constructor body `e == E::B(a)`, and the match body
/// `result == match e { E::A => 0u32, E::B(v) => v }`; assert the postcondition.
/// The syn lowerer resolves the `E::B(a)` constructor and the match's
/// testers/selectors on its own, so a verdict match validates the driver's
/// THIR-built enum construction + `Match` IR.
fn syn_enum_match_outcome(assert_cond: &str) -> Outcome {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", u32t());
    ctx.declare_var_typed("e", e_ty());
    ctx.declare_var_typed("result", u32t());
    ctx.push_obligation(ProofObligation::assume("requires_0", "a < 100"));
    ctx.push_obligation(ProofObligation::assume("body_e", "e == E::B(a)"));
    ctx.push_obligation(ProofObligation::assume(
        "body_r",
        "result == match e { E::A => 0u32, E::B(v) => v }",
    ));
    ctx.push_obligation(ProofObligation::assert("ensures_0", assert_cond));
    outcome_from(&ctx.verify())
}

#[test]
fn driver_thir_agrees_with_syn_on_enums_and_match() {
    let results = run_driver();

    // --- syn reference verdicts (the trusted, independent path) ---
    let syn_verify = syn_enum_match_outcome("result == a");
    let syn_refute = syn_enum_match_outcome("result == 0");

    // Non-degeneracy: the trusted side must land on the intended semantics, not a
    // degenerate "both Unknown". If the B-arm payload read were dropped (or the
    // arm matched the wrong variant), (b) would flip to Verified — the guard
    // catches that.
    assert_eq!(
        syn_verify,
        Outcome::Verified,
        "syn ref: match E::B(a) reads the payload a"
    );
    assert_eq!(
        syn_refute,
        Outcome::Refuted,
        "syn ref: match E::B(a) payload is not forced to 0"
    );

    // (a) TRUE payload read through a matched constructed value: driver == syn.
    let d_verify = find(&results, "enum_match_verify");
    assert_eq!(
        d_verify,
        &Ok(syn_verify.clone()),
        "enum_match_verify: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_verify, &Ok(Outcome::Verified));

    // (b) FALSE payload read: driver == syn == Refuted (per-arm constraint kept).
    let d_refute = find(&results, "enum_match_refute");
    assert_eq!(
        d_refute,
        &Ok(syn_refute.clone()),
        "enum_match_refute: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_refute, &Ok(Outcome::Refuted));

    // (c1) a match arm guard fails closed to UnsupportedContract.
    let d_guard = find(&results, "enum_match_guard_oof");
    assert!(
        matches!(d_guard, Err(DriverError::UnsupportedContract(_))),
        "enum_match_guard_oof must fail closed to UnsupportedContract, got {d_guard:?}"
    );

    // (c2) a wildcard/default arm (not one-arm-per-variant) fails closed.
    let d_wild = find(&results, "enum_match_wildcard_oof");
    assert!(
        matches!(d_wild, Err(DriverError::UnsupportedContract(_))),
        "enum_match_wildcard_oof must fail closed to UnsupportedContract, got {d_wild:?}"
    );
}

#[test]
fn driver_thir_agrees_with_syn_on_scalar_hoare() {
    let results = run_driver();

    // --- syn reference verdicts (the trusted path) ---
    let syn_verify = syn_outcome(
        &[("requires_0", "x < 100"), ("body", "result == x + 1")],
        &[("ensures_0", "result == x + 1")],
    );
    let syn_refute = syn_outcome(
        &[("requires_0", "x < 100"), ("body", "result == x + 1")],
        &[("ensures_0", "result == x + 2")],
    );

    // The syn path must itself land on the expected semantics (guards against a
    // degenerate "both Unknown" agreement).
    assert_eq!(syn_verify, Outcome::Verified, "syn reference (verify case)");
    assert_eq!(syn_refute, Outcome::Refuted, "syn reference (refute case)");

    // --- (a) true postcondition: driver verdict == syn verdict == Verified ---
    let driver_verify = find(&results, "verify_case");
    assert_eq!(
        driver_verify,
        &Ok(syn_verify.clone()),
        "verify_case: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(driver_verify, &Ok(Outcome::Verified));

    // --- (b) false postcondition: driver verdict == syn verdict == Refuted ---
    let driver_refute = find(&results, "refute_case");
    assert_eq!(
        driver_refute,
        &Ok(syn_refute.clone()),
        "refute_case: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(driver_refute, &Ok(Outcome::Refuted));

    // --- (c) out-of-fragment construct fails closed (not a fabricated verdict) ---
    let driver_oof = find(&results, "out_of_fragment_case");
    assert!(
        matches!(driver_oof, Err(DriverError::UnsupportedContract(_))),
        "out_of_fragment_case must fail closed to UnsupportedContract, got {driver_oof:?}"
    );
}

/// Attribute-block peeling: the shape the real `#[trust_vc::contract(..)]` /
/// `returns(..)` macro expansion produces under `--cfg trust_vc_driver` — an
/// OUTER transparent wrapper block whose sole content is an INNER contract block
/// `{ requires(..); let ret = 'lbl: { <body> }; ensures(..); ret }`, the `let ret`
/// initializer being a LABELED block. The driver must PEEL the transparent outer
/// wrapper (to find the markers) and the labeled value-block `let` initializer
/// (to its tail value), reaching the SAME verdict as the bare scalar-Hoare cases.
/// A value-break out of the labeled block, or an extra statement inside it, must
/// FAIL CLOSED — never assuming block == tail when a value-break could differ.
#[test]
fn driver_thir_agrees_with_syn_on_attribute_block_shape() {
    let results = run_driver();

    // --- syn reference verdicts (the trusted path; same content as verify/refute) ---
    let syn_verify = syn_outcome(
        &[("requires_0", "x < 100"), ("body", "result == x + 1")],
        &[("ensures_0", "result == x + 1")],
    );
    let syn_refute = syn_outcome(
        &[("requires_0", "x < 100"), ("body", "result == x + 1")],
        &[("ensures_0", "result == x + 2")],
    );

    // Non-degeneracy: the trusted side lands on the intended semantics, so a
    // vacuous/faked block peel would DISAGREE (b would flip to Verified).
    assert_eq!(syn_verify, Outcome::Verified, "syn ref (attr-block verify)");
    assert_eq!(syn_refute, Outcome::Refuted, "syn ref (attr-block refute)");

    // (a) TRUE post through the attribute-block shape: driver peels the outer
    // wrapper + the labeled `let` initializer and lowers the REAL body relation.
    let d_verify = find(&results, "attr_block_verify");
    assert_eq!(
        d_verify,
        &Ok(syn_verify.clone()),
        "attr_block_verify: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_verify, &Ok(Outcome::Verified));

    // (b) FALSE post: Refuted on both — proves the driver lowered the real body
    // value through the labeled block, not a vacuous constant `true`.
    let d_refute = find(&results, "attr_block_refute");
    assert_eq!(
        d_refute,
        &Ok(syn_refute.clone()),
        "attr_block_refute: driver THIR verdict must equal syn verdict"
    );
    assert_eq!(d_refute, &Ok(Outcome::Refuted));

    // (c1) a value-break out of the labeled block fails closed. The block value
    // comes from `break 'lbl (x + 5)`, which could differ from the tail; the
    // strict whitelist rejects ExprKind::Break so the whole contract refuses.
    let d_break = find(&results, "attr_block_value_break_oof");
    assert!(
        matches!(d_break, Err(DriverError::UnsupportedContract(_))),
        "attr_block_value_break_oof must fail closed to UnsupportedContract, got {d_break:?}"
    );

    // (c2) an extra/side-effecting statement inside the labeled block fails
    // closed (the value-block peel requires empty statements).
    let d_stmt = find(&results, "attr_block_stmt_oof");
    assert!(
        matches!(d_stmt, Err(DriverError::UnsupportedContract(_))),
        "attr_block_stmt_oof must fail closed to UnsupportedContract, got {d_stmt:?}"
    );
}
