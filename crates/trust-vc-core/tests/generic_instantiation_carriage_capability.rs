// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// quality-audit: allow-file allow-rust-size — one liar/twin matrix per instantiation shape
//! SOUNDNESS PIN (H10): a call to a GENERIC source function may
//! lower only when its solver term determines the instantiation, or when the
//! function's value provably does not depend on it.
//!
//! A source fn call used to lower to `FnCall { name, args, return_ty }` — the
//! turbofish was read only to substitute a bare `TypeParam` return type, and
//! the encoder's only per-instantiation carrier is the type-keyed `Box_T` at a
//! value parameter whose registered type is exactly `TypeParam(T)`. So every
//! instantiation the ARGUMENTS did not already separate collapsed into ONE
//! uninterpreted symbol, and the engine proved equalities Rust refutes:
//!
//! * `tid::<usize>() == tid::<u64>()` for a bodyless `fn tid<T>() -> int;`
//!   (and u32/u64, bool/u8, isize/i64, usize/u32, a valued `tid2::<A>(0)`, a
//!   module-qualified `m::qid::<u8>() == m::qid::<u64>()`, and a second
//!   parameter no argument carries, `two::<u8, u8>(0u8) == two::<u8, u16>(0u8)`);
//! * a fact pinned about `tid::<u8>()` transferred to `tid::<u64>()`;
//! * a requires-linked witness whose satisfying model (tid::<u8> = 1,
//!   tid::<u64> = 2, r = 5) falsifies the verified assert;
//! * the rustc-valid `#[opaque] fn csz<T: Sz>() -> usize { T::N }` proved
//!   `csz::<u8>() == csz::<u64>()` (1 == 8) and a panicking `arr[r]` body;
//! * a `tid3::<u8>/<u64>` projection pair proved `a == b` while the plain-Rust
//!   realization panics with a = 1, b = 0;
//! * an exec sibling `ereq_c<T>() -> u64 { size_of::<T>() as u64 }` whose body
//!   axiom a `requires` clause suppresses proved `ereq_c::<u8>() ==
//!   ereq_c::<u64>()` (1 != 8 at runtime) with no spec fn at all;
//! * nested-only (`PhantomData<T>`, `Option<T>`), return-only (`-> Seq<T>`)
//!   and const generics (`cz::<3>() == cz::<4>()`), a generic caller mixing
//!   `tid::<T>()` with `tid::<u8>()`, and an unsuffixed literal at a carried
//!   position (`bare::<u8>(0) == bare::<u16>(0)` lowered both to `Box_i32(0)`);
//! * an impl-less trait default body `tid::<u8>() == tid::<u64>()` (or the exec
//!   `ereq` pair) Verified its `ensures(result)` conformance obligation.
//!
//! THE RULE, as now enforced.
//! 1. Carriage at declaration: every generic parameter must be the exact
//!    registered type of a value parameter (or be bound by the catalog's
//!    per-query datatype monomorphization). Otherwise the declaration is
//!    REFUSED at every helper-registration site unless its definitional axiom
//!    is published unconditionally (a transparent spec body that is not
//!    opaque, not uninterp and not recursion-suppressed) — that body is lowered
//!    in the erased environment, so it is T-uniform.
//! 2. Faithful carrier at the call site: each turbofish argument is mapped onto
//!    its declared generic parameter in DECLARATION order (recorded by the
//!    carriage-checked registration); at every position carrying that
//!    parameter an unsuffixed literal is coerced to the instantiation and an
//!    argument of any other type fails closed. A turbofish that does not
//!    instantiate every declared parameter fails closed, and so does a
//!    multi-argument turbofish over a helper whose registration recorded no
//!    order.
//! 3. No shadowed parameter: the lowering has no generic scope, so a generic
//!    parameter spelled like a type or value it resolves (`type T = u8;`, a
//!    builtin such as `u8`, a const `N`) was read AS that item — `fn tsz<T>()
//!    -> usize { size_of::<T>() }` published `tsz() == 1` for every
//!    instantiation, the very premise rule 1's exemption rests on. Such a
//!    declaration is refused wherever the collision is spelled.
//!
//! 4. The METHOD half. A registered method call lowers to
//!    `uf_name(receiver, args…)` and `mc.turbofish` was read by NOTHING, so a
//!    method-level generic collapsed exactly as a free function's did:
//!    `t.k::<u8>() == t.k::<u64>()` for `#[trust_vc::trait_spec] trait Tr { fn
//!    k<P>(&self) -> u64; }` Verified, including the `arr[b as usize]` path it
//!    made unreachable, and so did the `#[trust_vc::spec]`, concrete-impl,
//!    return-only and defaulted spellings. A method generic no value parameter
//!    carries now fails EVERY call closed — with a turbofish or without one,
//!    since inference picks an instantiation the term cannot show — and a
//!    CARRIED one takes the same call-site faithfulness check as a free
//!    function (`t.m::<u8>(0)` vs `t.m::<u16>(0)` boxed both literals as `i32`
//!    and Verified; now refuted). The declaration is NOT refused: a trait
//!    method's UF and its quantified postcondition axiom are shared by every
//!    impl and published whether or not anything calls it, so refusing there
//!    would poison files whose generic method is never used. A registration
//!    that records no declaration order (an accessor, an inherent method)
//!    accepts no explicit turbofish at all — `.collect::<Vec<_>>()` in
//!    `evals/verus/ported/hash.rs` is untouched because it resolves to no
//!    registered method.
//! 5. The MACRO lane (`#[trust_vc::spec]` expansion) declines the same
//!    declaration: it registers a helper keyed by name and arguments with no
//!    per-query gate to decline, so an uncarried generic whose body axiom is
//!    not published for every use (opaque, recursion-suppressed, unit-returning)
//!    is a compile error there. MEASURED liar, Verified before the refusal:
//!    `#[spec] fn rsz<T>(n: u64) -> u64 { if n == 0 { size_of::<T>() as u64 }
//!    else { rsz::<T>(n - 1) } }` (recursive, no `decreases`, so its body is
//!    never lowered) proved `rsz::<u8>(0) == rsz::<u64>(0)`, which Rust refutes
//!    1 != 8. Pinned by `tests/compile-fail/spec_generic_instantiation_not_carried.rs`
//!    in the `trust-vc` crate, whose carried and T-uniform controls still compile.
//!
//! NOT COVERED, measured open and left for a follow-up rather than closed
//! blind: BACKWARD LITERAL TYPE INFERENCE. `let a = 0; let _b: u8 =
//! a; bare(a) == bare(0i32)` still Verifies, although Rust infers `a: u8` and
//! therefore reads the two calls at DIFFERENT instantiations. The call-site
//! rule rests on "without a turbofish, the argument's own type is Rust's
//! inference", which this refutes; closing it needs the lowering to honour
//! backward literal inference, not a carriage rule.
//!
//! MEASURED on the engine before this fix (VC cache off): every `l*`
//! liar in this file returned `Verified`, except `l17`/`l25` (Counterexample
//! through their transparent bodies); the L29 conformance obligation returned
//! `Verified` there too, and L30's was measured `Verified` with only the
//! default-body gate mutated out. The controls `c1_unsuffixed_same_instantiation`,
//! `c1_reversed_positions_map_by_declaration_order` and
//! `c2_pinned_value_transfers_within_instantiation` were Counterexamples there:
//! an unsuffixed literal at a carrying position was boxed as `i32`.
//!
//! Every liar below is REFUTED (Counterexample) or REFUSED with the new
//! `generic instantiation not carried` / `generic parameter shadowed` detail —
//! never an unrelated Error. The
//! controls pin that the refusal is not blanket: carried same-instantiation
//! uses verify, typed cross-instantiation uses stay refuted, transparent
//! T-uniform bodies still verify both ways. The price is pinned too
//! (same-instantiation uses of a refused fn are an Error), so re-admitting them
//! is a deliberate change.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const REFUSAL: &str = "generic instantiation not carried";
const SHADOWED: &str = "generic parameter shadowed";

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    // Every verdict below is a fresh solve: a cached verdict from an engine that
    // still collapsed instantiations must never answer for this one.
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    // One file per (fixture, function): the tests run on parallel threads and
    // several of them verify different functions of one fixture.
    p.push(format!(
        "tvc_h10_carriage_{}_{}_{}.rs",
        std::process::id(),
        tmp_id,
        func
    ));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    eprintln!("H10 {tmp_id}::{func}: {result:?}");
    result
}

/// Collects every mismatch of one test so a single run reports the whole
/// verdict table instead of stopping at the first surprise.
#[derive(Default)]
struct Pins {
    failures: Vec<String>,
}

impl Pins {
    fn refused(&mut self, result: VerifyResult, callee: &str) {
        match &result {
            VerifyResult::Error { message }
                if message.contains(REFUSAL) && message.contains(&format!("`{callee}`")) => {}
            other => self.failures.push(format!(
                "expected the `{REFUSAL}` refusal naming `{callee}`, got {other:?}"
            )),
        }
    }

    fn shadowed(&mut self, result: VerifyResult, callee: &str) {
        match &result {
            VerifyResult::Error { message }
                if message.contains(SHADOWED) && message.contains(&format!("`{callee}`")) => {}
            other => self.failures.push(format!(
                "expected the `{SHADOWED}` refusal naming `{callee}`, got {other:?}"
            )),
        }
    }

    fn counterexample(&mut self, result: VerifyResult) {
        if !matches!(result, VerifyResult::Counterexample { .. }) {
            self.failures
                .push(format!("expected Counterexample, got {result:?}"));
        }
    }

    fn verified(&mut self, result: VerifyResult) {
        if !matches!(result, VerifyResult::Verified) {
            self.failures
                .push(format!("expected Verified, got {result:?}"));
        }
    }

    /// Fail-closed refusals of any spelling are acceptable here; only a
    /// `Verified` is a failure.
    fn not_verified(&mut self, result: VerifyResult) {
        if matches!(result, VerifyResult::Verified) {
            self.failures
                .push("expected a non-Verified verdict, got Verified".to_string());
        }
    }

    #[track_caller]
    fn finish(self) {
        assert!(
            self.failures.is_empty(),
            "{} pin(s) failed:\n{}",
            self.failures.len(),
            self.failures.join("\n")
        );
    }
}

// ---------------------------------------------------------------------------
// L1/L2/L17/C3/C12 — a type-parameter-only bodyless spec fn.
// ---------------------------------------------------------------------------
const TID: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn tid<T>() -> int;

#[trust_vc::spec]
fn tid2<T>(x: int) -> int;

#[trust_vc::spec]
fn tsz<T>() -> int {
    5
}

type Alias64 = u64;

mod m {
    use trust_vc_types::int;

    #[trust_vc::spec]
    pub fn qid<T>() -> int;
}

#[trust_vc::ensures(true)]
fn l1_module_qualified_u8_eq_u64() {
    trust_vc::assert!(m::qid::<u8>() == m::qid::<u64>());
}

#[trust_vc::ensures(true)]
fn l1_usize_eq_u64() {
    trust_vc::assert!(tid::<usize>() == tid::<u64>());
}

#[trust_vc::ensures(true)]
fn l1_u32_eq_u64() {
    trust_vc::assert!(tid::<u32>() == tid::<u64>());
}

#[trust_vc::ensures(true)]
fn l1_bool_eq_u8() {
    trust_vc::assert!(tid::<bool>() == tid::<u8>());
}

#[trust_vc::ensures(true)]
fn l1_isize_eq_i64() {
    trust_vc::assert!(tid::<isize>() == tid::<i64>());
}

#[trust_vc::ensures(true)]
fn l1_usize_eq_u32() {
    trust_vc::assert!(tid::<usize>() == tid::<u32>());
}

#[trust_vc::ensures(true)]
fn l2_valued_usize_eq_u64() {
    trust_vc::assert!(tid2::<usize>(0) == tid2::<u64>(0));
}

#[trust_vc::ensures(true)]
fn l17_transparent_body_liar() {
    trust_vc::assert!(tsz::<u8>() == 6);
}

#[trust_vc::ensures(true)]
fn c3_transparent_body_value() {
    trust_vc::assert!(tsz::<u8>() == 5);
}

#[trust_vc::ensures(true)]
fn c3_transparent_body_cross_instantiation() {
    trust_vc::assert!(tsz::<u8>() == tsz::<u64>());
}

#[trust_vc::ensures(true)]
fn c12_same_instantiation() {
    trust_vc::assert!(tid::<u64>() == tid::<u64>());
}

#[trust_vc::ensures(true)]
fn c12_alias_same_instantiation() {
    trust_vc::assert!(tid::<Alias64>() == tid::<u64>());
}

#[trust_vc::ensures(true)]
fn c12_generic_caller_same<T>() {
    trust_vc::assert!(tid::<T>() == tid::<T>());
}

#[trust_vc::ensures(true)]
fn l14_generic_caller_mixes_instantiations<T>() {
    trust_vc::assert!(tid::<T>() == tid::<u8>());
}
"#;

#[test]
fn type_param_only_spec_fn_instantiations_are_refused() {
    let mut pins = Pins::default();
    for func in [
        "l1_usize_eq_u64",
        "l1_u32_eq_u64",
        "l1_bool_eq_u8",
        "l1_isize_eq_i64",
        "l1_usize_eq_u32",
    ] {
        pins.refused(verify("tid", func, TID), "tid");
    }
    pins.refused(verify("tid", "l2_valued_usize_eq_u64", TID), "tid2");
    pins.refused(
        verify("tid", "l1_module_qualified_u8_eq_u64", TID),
        "m::qid",
    );
    pins.refused(
        verify("tid", "l14_generic_caller_mixes_instantiations", TID),
        "tid",
    );
    pins.finish();
}

#[test]
fn transparent_type_uniform_body_is_exempt_and_still_refutes() {
    let mut pins = Pins::default();
    pins.counterexample(verify("tid", "l17_transparent_body_liar", TID));
    pins.verified(verify("tid", "c3_transparent_body_value", TID));
    pins.verified(verify(
        "tid",
        "c3_transparent_body_cross_instantiation",
        TID,
    ));
    pins.finish();
}

#[test]
fn documented_incompleteness_same_instantiation_uses_of_refused_fns() {
    let mut pins = Pins::default();
    // The price of the rule: without per-instantiation symbols a refused
    // declaration cannot be used even at ONE instantiation. Re-admitting these
    // must be a deliberate change (Verus-style type arguments as term args).
    pins.refused(verify("tid", "c12_same_instantiation", TID), "tid");
    pins.refused(verify("tid", "c12_alias_same_instantiation", TID), "tid");
    pins.refused(verify("tid", "c12_generic_caller_same", TID), "tid");
    pins.finish();
}

// ---------------------------------------------------------------------------
// L3/L4/L7 — cross-instantiation facts through contracts.
// ---------------------------------------------------------------------------
const PINS: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn tid<T>() -> int;

#[trust_vc::spec]
fn tid3<T>(x: int) -> int;

#[trust_vc::external_body]
#[trust_vc::ensures(tid::<u8>() == 1)]
fn pin_u8() {}

#[trust_vc::ensures(true)]
fn l3_cross_instantiation_derived() {
    pin_u8();
    trust_vc::assert!(tid::<u64>() == 1);
}

#[trust_vc::requires(tid::<u8>() == 1)]
#[trust_vc::requires((tid::<u64>() == 1) == (r == 0u64))]
#[trust_vc::ensures(true)]
fn l4_requires_linked(r: u64) {
    trust_vc::assert!(r == 0u64);
}

#[trust_vc::external_body]
#[trust_vc::ensures(result as int == tid3::<u8>(x as int))]
fn proj_u8(x: u64) -> u64 {
    x
}

#[trust_vc::external_body]
#[trust_vc::ensures(result as int == tid3::<u64>(x as int))]
fn proj_u64(x: u64) -> u64 {
    0u64
}

#[trust_vc::ensures(true)]
fn l7_runtime_projection_witness(x: u64) {
    let a = proj_u8(x);
    let b = proj_u64(x);
    trust_vc::assert!(a == b);
}
"#;

#[test]
fn cross_instantiation_contract_facts_are_refused() {
    let mut pins = Pins::default();
    pins.refused(
        verify("pins", "l3_cross_instantiation_derived", PINS),
        "tid",
    );
    pins.refused(verify("pins", "l4_requires_linked", PINS), "tid");
    pins.refused(
        verify("pins", "l7_runtime_projection_witness", PINS),
        "tid3",
    );
    pins.finish();
}

// ---------------------------------------------------------------------------
// L5/L6 — rustc-valid opaque body over an associated const (judge K5/K6).
// ---------------------------------------------------------------------------
const CSZ: &str = r#"
pub trait Sz {
    const N: usize;
}
impl Sz for u8 {
    const N: usize = 1;
}
impl Sz for u64 {
    const N: usize = 8;
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn csz<T: Sz>() -> usize {
    T::N
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn dsz<T: Sz>() -> usize {
    T::N
}

#[trust_vc::contract(requires(true))]
fn l5_opaque_u8_eq_u64() {
    trust_vc::assert!(csz::<u8>() == csz::<u64>());
}

#[trust_vc::contract(requires(csz::<u8>() == 1usize, (csz::<u64>() == 1usize) == (r == 0usize)))]
fn l6_requires_linked_index_panics(r: usize) {
    let arr = [0u8; 1];
    let _x = arr[r];
}

#[trust_vc::contract(requires(true))]
fn l5_distinct_opaque_fns_same_instantiation() {
    trust_vc::assert!(csz::<u8>() == dsz::<u8>());
}
"#;

#[test]
fn opaque_associated_const_body_instantiations_are_refused() {
    let mut pins = Pins::default();
    pins.refused(verify("csz", "l5_opaque_u8_eq_u64", CSZ), "csz");
    pins.refused(verify("csz", "l6_requires_linked_index_panics", CSZ), "csz");
    // Formerly a Counterexample through two distinct uninterpreted symbols; the
    // opaque declarations are now refused before any symbol exists.
    pins.refused(
        verify("csz", "l5_distinct_opaque_fns_same_instantiation", CSZ),
        "csz",
    );
    pins.finish();
}

// ---------------------------------------------------------------------------
// L8/L9 — exec sibling helpers whose body axiom a requires clause suppresses.
// ---------------------------------------------------------------------------
const EXEC: &str = r#"
#[trust_vc::contract(requires(true))]
fn ereq_c<T>() -> u64 {
    core::mem::size_of::<T>() as u64
}

#[trust_vc::requires(true)]
fn ereq<T>() -> u64 {
    core::mem::size_of::<T>() as u64
}

#[trust_vc::requires(true)]
fn eopt<T>(o: Option<T>) -> u64 {
    core::mem::size_of::<T>() as u64
}

fn esz<T>() -> u64 {
    core::mem::size_of::<T>() as u64
}

#[trust_vc::ensures(true)]
fn l8_exec_published_body_depends_on_instantiation() {
    let a = esz::<u8>();
    let b = esz::<u64>();
    trust_vc::assert!(a == b);
}

#[trust_vc::contract(requires(true))]
fn l8_exec_contract_requires_sizes_eq() {
    let a = ereq_c::<u8>();
    let b = ereq_c::<u64>();
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l8_exec_requires_attr_sizes_eq() {
    let a = ereq::<u8>();
    let b = ereq::<u64>();
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l9_exec_option_param_sizes_eq() {
    let a = eopt::<u8>(None);
    let b = eopt::<u64>(None);
    trust_vc::assert!(a == b);
}
"#;

#[test]
fn exec_sibling_without_published_body_is_refused() {
    let mut pins = Pins::default();
    pins.refused(
        verify("exec", "l8_exec_contract_requires_sizes_eq", EXEC),
        "ereq_c",
    );
    pins.refused(
        verify("exec", "l8_exec_requires_attr_sizes_eq", EXEC),
        "ereq",
    );
    pins.refused(
        verify("exec", "l9_exec_option_param_sizes_eq", EXEC),
        "eopt",
    );
    // A requires-free sibling has its body PUBLISHED, so `esz` passes the
    // carriage gate as instantiation-uniform — and the premise holds: the
    // instantiation-dependent `size_of::<T>()` cannot lower in the erased
    // environment, so the query fails closed (1 != 8 at runtime).
    pins.not_verified(verify(
        "exec",
        "l8_exec_published_body_depends_on_instantiation",
        EXEC,
    ));
    pins.finish();
}

// ---------------------------------------------------------------------------
// L10-L13 — nested-only, return-only and const generics are not carriers.
// ---------------------------------------------------------------------------
const NESTED: &str = r#"
use trust_vc_types::{int, Seq};
use core::marker::PhantomData;

#[trust_vc::spec]
fn pd<T>(p: PhantomData<T>) -> int;

#[trust_vc::spec]
fn op<T>(o: Option<T>) -> int;

#[trust_vc::spec]
fn pick<T>() -> Seq<T>;

#[trust_vc::spec]
fn cz<const N: usize>() -> int;

#[trust_vc::ensures(true)]
fn l10_phantomdata_inferred() {
    let a: PhantomData<u8> = PhantomData;
    let b: PhantomData<u64> = PhantomData;
    trust_vc::assert!(pd(a) == pd(b));
}

#[trust_vc::ensures(true)]
fn l10_phantomdata_turbofish() {
    trust_vc::assert!(pd::<u8>(PhantomData) == pd::<u64>(PhantomData));
}

#[trust_vc::ensures(true)]
fn l11_option_only_param() {
    trust_vc::assert!(op::<u8>(None) == op::<u64>(None));
}

#[trust_vc::ensures(true)]
fn l12_return_nested() {
    trust_vc::assert!(pick::<u8>().len() == pick::<u64>().len());
}

#[trust_vc::ensures(true)]
fn l13_const_generic() {
    trust_vc::assert!(cz::<3>() == cz::<4>());
}
"#;

#[test]
fn nested_return_and_const_generics_are_refused() {
    let mut pins = Pins::default();
    pins.refused(verify("nested", "l10_phantomdata_inferred", NESTED), "pd");
    pins.refused(verify("nested", "l10_phantomdata_turbofish", NESTED), "pd");
    pins.refused(verify("nested", "l11_option_only_param", NESTED), "op");
    pins.refused(verify("nested", "l12_return_nested", NESTED), "pick");
    pins.refused(verify("nested", "l13_const_generic", NESTED), "cz");
    pins.finish();
}

// ---------------------------------------------------------------------------
// L15/L16/C1/C2 — the carried position must faithfully carry the turbofish.
// ---------------------------------------------------------------------------
const BARE: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn bare<T>(x: T) -> int;

#[trust_vc::spec]
fn bare2<T>(x: T, n: int) -> int;

#[trust_vc::spec]
fn first2<A, B>(a: A, b: B) -> int;

#[trust_vc::spec]
fn two<A, B>(a: A) -> int;

#[trust_vc::spec]
fn rev<A, B>(b: B, a: A) -> int;

#[trust_vc::external_body]
#[trust_vc::ensures(bare::<u8>(0u8) == 1)]
fn pin_bare8() {}

#[trust_vc::ensures(true)]
fn l15_unsuffixed_u8_u16() {
    trust_vc::assert!(bare::<u8>(0) == bare::<u16>(0));
}

#[trust_vc::ensures(true)]
fn l15_unsuffixed_u8_u64() {
    trust_vc::assert!(bare::<u8>(0) == bare::<u64>(0));
}

#[trust_vc::ensures(true)]
fn l15_two_param_unsuffixed() {
    trust_vc::assert!(bare2::<u8>(1, 0) == bare2::<i32>(1, 0));
}

#[trust_vc::ensures(true)]
fn l16_two_turbofish_args() {
    trust_vc::assert!(first2::<u8, u16>(0, 0) == first2::<u16, u8>(0, 0));
}

#[trust_vc::ensures(true)]
fn l16_two_turbofish_args_typed_let_literal() {
    let a = 0;
    trust_vc::assert!(first2::<u8, u16>(a, 0u16) == first2::<i32, u16>(0i32, 0u16));
}

#[trust_vc::ensures(true)]
fn c2_two_turbofish_args_typed_cross_instantiation() {
    trust_vc::assert!(first2::<u8, u16>(0u8, 0u16) == first2::<u16, u8>(0u16, 0u8));
}

#[trust_vc::ensures(true)]
fn c1_two_turbofish_args_typed_same_instantiation(x: u8, y: u16) {
    trust_vc::assert!(first2::<u8, u16>(x, y) == first2::<u8, u16>(x, y));
}

#[trust_vc::ensures(true)]
fn b1_turbofish_order_disagrees_with_argument_types() {
    trust_vc::assert!(first2::<u16, u8>(0u8, 0u16) == first2::<u16, u8>(0u8, 0u16));
}

#[trust_vc::ensures(true)]
fn b2_turbofish_argument_count_mismatch() {
    trust_vc::assert!(first2::<u8>(0u8, 0u16) == first2::<u8>(0u8, 0u16));
}

#[trust_vc::ensures(true)]
fn l16_reversed_positions_unsuffixed_cross_instantiation() {
    trust_vc::assert!(rev::<u8, u16>(0, 0) == rev::<u16, u8>(0, 0));
}

#[trust_vc::ensures(true)]
fn c1_reversed_positions_map_by_declaration_order() {
    trust_vc::assert!(rev::<u8, u16>(0u16, 0u8) == rev::<u8, u16>(0, 0));
}

#[trust_vc::ensures(true)]
fn l18_second_type_param_uncarried() {
    trust_vc::assert!(two::<u8, u8>(0u8) == two::<u8, u16>(0u8));
}

#[trust_vc::ensures(true)]
fn c1_same_instantiation(x: u8) {
    trust_vc::assert!(bare::<u8>(x) == bare::<u8>(x));
}

#[trust_vc::ensures(true)]
fn c1_unsuffixed_same_instantiation() {
    trust_vc::assert!(bare::<u8>(0) == bare::<u8>(0u8));
}

#[trust_vc::ensures(true)]
fn c2_typed_cross_instantiation() {
    trust_vc::assert!(bare::<u8>(0u8) == bare::<u64>(0u64));
}

#[trust_vc::ensures(true)]
fn c2_typed_derived() {
    pin_bare8();
    trust_vc::assert!(bare::<u64>(0u64) == 1);
}

#[trust_vc::ensures(true)]
fn c2_usize_vs_u64() {
    trust_vc::assert!(bare::<usize>(0usize) == bare::<u64>(0u64));
}

#[trust_vc::ensures(true)]
fn c2_pinned_value_transfers_within_instantiation() {
    pin_bare8();
    trust_vc::assert!(bare::<u8>(0) == 1);
}
"#;

#[test]
fn carried_position_faithfully_carries_the_turbofish() {
    let mut pins = Pins::default();
    pins.counterexample(verify("bare", "l15_unsuffixed_u8_u16", BARE));
    pins.counterexample(verify("bare", "l15_unsuffixed_u8_u64", BARE));
    pins.counterexample(verify("bare", "l15_two_param_unsuffixed", BARE));
    // Two explicit arguments are mapped onto the declared parameters in
    // DECLARATION order, and each unsuffixed literal is coerced to its own
    // instantiation (`Box_u8(0), Box_u16(0)` vs `Box_u16(0), Box_u8(0)`).
    pins.counterexample(verify("bare", "l16_two_turbofish_args", BARE));
    // The `let a = 0;` binding is `u8` in Rust (inferred from the turbofish) but
    // lowered as `i32`, which matched the `0i32` of the other instantiation. The
    // literal now reaches the carrying position and is coerced to `u8`.
    pins.counterexample(verify(
        "bare",
        "l16_two_turbofish_args_typed_let_literal",
        BARE,
    ));
    // Boundary (not liars — both sides are one term): an argument whose type
    // disagrees with the turbofish slot it maps to, and a turbofish that does
    // not instantiate every declared parameter, fail closed rather than guess.
    pins.refused(
        verify(
            "bare",
            "b1_turbofish_order_disagrees_with_argument_types",
            BARE,
        ),
        "first2",
    );
    pins.refused(
        verify("bare", "b2_turbofish_argument_count_mismatch", BARE),
        "first2",
    );
    // Positions listed in the opposite order to the generics: the mapping is by
    // declaration, never by first appearance among the value parameters.
    pins.counterexample(verify(
        "bare",
        "l16_reversed_positions_unsuffixed_cross_instantiation",
        BARE,
    ));
    // A carried FIRST parameter does not excuse an uncarried second one.
    pins.refused(
        verify("bare", "l18_second_type_param_uncarried", BARE),
        "two",
    );
    pins.finish();
}

#[test]
fn carried_generic_controls_stay_exact() {
    let mut pins = Pins::default();
    pins.verified(verify("bare", "c1_same_instantiation", BARE));
    pins.verified(verify("bare", "c1_unsuffixed_same_instantiation", BARE));
    pins.verified(verify(
        "bare",
        "c2_pinned_value_transfers_within_instantiation",
        BARE,
    ));
    pins.counterexample(verify("bare", "c2_typed_cross_instantiation", BARE));
    pins.verified(verify(
        "bare",
        "c1_two_turbofish_args_typed_same_instantiation",
        BARE,
    ));
    pins.counterexample(verify(
        "bare",
        "c2_two_turbofish_args_typed_cross_instantiation",
        BARE,
    ));
    pins.verified(verify(
        "bare",
        "c1_reversed_positions_map_by_declaration_order",
        BARE,
    ));
    pins.counterexample(verify("bare", "c2_typed_derived", BARE));
    pins.counterexample(verify("bare", "c2_usize_vs_u64", BARE));
    pins.finish();
}

// ---------------------------------------------------------------------------
// L19/L20 — lemma ensures and quantified bodies reach the same refusal.
// ---------------------------------------------------------------------------
const LEMMA: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn tid<T>() -> int;

#[trust_vc::proof]
#[trust_vc::ensures(tid::<u8>() == tid::<u64>())]
fn l19_lemma_ensures_collapse() {}

#[trust_vc::ensures(true)]
fn l20_quantified_collapse(x: u64) {
    trust_vc::assert!(forall(|i: int| tid::<u8>() + i == tid::<u64>() + i));
}
"#;

#[test]
fn lemma_and_quantified_uses_are_refused() {
    let mut pins = Pins::default();
    pins.refused(verify("lemma", "l19_lemma_ensures_collapse", LEMMA), "tid");
    pins.refused(verify("lemma", "l20_quantified_collapse", LEMMA), "tid");
    pins.finish();
}

// ---------------------------------------------------------------------------
// L21-L24 — a generic parameter SHADOWED by a type the lowering resolves. The
// environment has no generic scope, so `T` inside `fn tsz<T>` was read as the
// file's `type T = u8;`, and the "instantiation-uniform" published body said
// `tsz() == 1` for every instantiation — a false verify even at ONE
// instantiation, and the premise the transparent-body exemption rests on.
// ---------------------------------------------------------------------------
const SHADOW: &str = r#"
use trust_vc_types::int;

type T = u8;

#[trust_vc::spec]
fn tsz<T>() -> usize {
    core::mem::size_of::<T>()
}

fn esz<T>() -> usize {
    core::mem::size_of::<T>()
}

fn cid<T>(x: T) -> usize {
    core::mem::size_of::<T>()
}

#[allow(non_camel_case_types)]
#[trust_vc::spec]
fn pu<u8>() -> usize {
    core::mem::size_of::<u8>()
}

#[trust_vc::ensures(true)]
fn l21_alias_shadowed_transparent_spec() {
    trust_vc::assert!(tsz::<u64>() == 1usize);
}

#[trust_vc::ensures(true)]
fn l22_alias_shadowed_exec_sibling() {
    let a = esz::<u64>();
    trust_vc::assert!(a == 1usize);
}

#[trust_vc::ensures(true)]
fn l23_alias_shadowed_carried_exec_sibling() {
    let a = cid::<u64>(5);
    trust_vc::assert!(a == 1usize);
}

#[trust_vc::ensures(true)]
fn l24_generic_named_like_a_primitive() {
    trust_vc::assert!(pu::<u64>() == 1usize);
}
"#;

#[test]
fn shadowed_generic_parameters_are_refused() {
    let mut pins = Pins::default();
    pins.shadowed(
        verify("shadow", "l21_alias_shadowed_transparent_spec", SHADOW),
        "tsz",
    );
    pins.shadowed(
        verify("shadow", "l22_alias_shadowed_exec_sibling", SHADOW),
        "esz",
    );
    pins.shadowed(
        verify("shadow", "l23_alias_shadowed_carried_exec_sibling", SHADOW),
        "cid",
    );
    pins.shadowed(
        verify("shadow", "l24_generic_named_like_a_primitive", SHADOW),
        "pu",
    );
    pins.finish();
}

// ---------------------------------------------------------------------------
// C13/C14 — the exemption still has power: transparent and termination-admitted
// recursive bodies over an uncarried parameter verify both ways and refute
// liars; a const generic is never exempt (its value IS the instantiation).
// ---------------------------------------------------------------------------
const EXEMPT: &str = r#"
use trust_vc_types::{int, nat};

#[trust_vc::spec]
fn usp<T>(x: int) -> int {
    x
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn rec<T>(n: nat) -> int {
    if n == 0 { 0 } else { rec::<T>((n - 1) as nat) }
}

#[trust_vc::spec]
fn cn<const N: usize>() -> usize {
    N
}

#[trust_vc::ensures(true)]
fn l25_transparent_uncarried_param_liar() {
    trust_vc::assert!(usp::<u8>(1) == 2);
}

#[trust_vc::ensures(true)]
fn c13_transparent_uncarried_param_cross_instantiation() {
    trust_vc::assert!(usp::<u8>(1) == usp::<u64>(1));
}

#[trust_vc::ensures(true)]
fn c13_recursive_uncarried_cross_instantiation() {
    trust_vc::assert!(rec::<u8>(3) == rec::<u64>(3));
}

#[trust_vc::ensures(true)]
fn c14_const_generic_transparent_value() {
    trust_vc::assert!(cn::<3>() == 3usize);
}
"#;

#[test]
fn unconditional_definitions_keep_their_power() {
    let mut pins = Pins::default();
    pins.counterexample(verify(
        "exempt",
        "l25_transparent_uncarried_param_liar",
        EXEMPT,
    ));
    pins.verified(verify(
        "exempt",
        "c13_transparent_uncarried_param_cross_instantiation",
        EXEMPT,
    ));
    pins.verified(verify(
        "exempt",
        "c13_recursive_uncarried_cross_instantiation",
        EXEMPT,
    ));
    // Documented incompleteness: TrustVc does not model const generic values.
    pins.refused(
        verify("exempt", "c14_const_generic_transparent_value", EXEMPT),
        "cn",
    );
    pins.finish();
}

// ---------------------------------------------------------------------------
// L26-L28 — a turbofish naming an instantiation the per-query datatype
// monomorphization did not pick. `gop` is carried by `GList<T>` only through
// the one concrete carrier the constructors show (`GList<i32>`); the un-inferred
// `GList::GNil` of `gop::<u8>(..)` lowered onto that carrier and collapsed with
// `gop::<i32>(..)`.
// ---------------------------------------------------------------------------
const MONO: &str = r#"
use trust_vc_types::int;

enum GList<T> {
    GNil,
    GCons(T, Box<GList<T>>),
}

#[trust_vc::spec]
fn gop<T>(xs: GList<T>) -> int;

#[trust_vc::ensures(true)]
fn l26_turbofish_hidden_instantiation() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    trust_vc::assert!(gop::<u8>(GList::GNil) == gop::<i32>(GList::GNil));
}

#[trust_vc::requires(gop::<u8>(GList::GNil) == 1)]
#[trust_vc::ensures(true)]
fn l27_turbofish_hidden_in_contract() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    trust_vc::assert!(gop::<i32>(GList::GNil) == 1);
}

#[trust_vc::contract(requires(gop::<u8>(GList::GNil) == 1), ensures(true))]
fn l27_turbofish_hidden_in_multi_clause_contract() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    trust_vc::assert!(gop::<i32>(GList::GNil) == 1);
}

"#;

// C15 lives in a fixture with NO disagreeing hint: a turbofish hint anywhere
// in the file (a contract, a spec body) widens the whole file's analysis, so
// the control that the refusal is not blanket must stand where none is spelled.
const MONO_AGREE: &str = r#"
use trust_vc_types::int;

enum GList<T> {
    GNil,
    GCons(T, Box<GList<T>>),
}

#[trust_vc::spec]
fn gop<T>(xs: GList<T>) -> int;

#[trust_vc::ensures(true)]
fn c15_turbofish_agrees_with_carrier() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    trust_vc::assert!(gop::<i32>(GList::GNil) == gop::<i32>(GList::GNil));
}
"#;

// A spec body's turbofish widens the whole file's analysis, exactly like its
// constructors do, so it lives in its own fixture (it would also refuse C15).
const MONO_BODY: &str = r#"
use trust_vc_types::int;

enum GList<T> {
    GNil,
    GCons(T, Box<GList<T>>),
}

#[trust_vc::spec]
fn gop<T>(xs: GList<T>) -> int;

#[trust_vc::spec]
fn via_u8() -> int {
    gop::<u8>(GList::GNil)
}

#[trust_vc::ensures(true)]
fn l28_turbofish_hidden_in_spec_body() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    trust_vc::assert!(via_u8() == gop::<i32>(GList::GNil));
}
"#;

// A CALLEE's contract is assumed at its call sites, so a turbofish spelled in
// a sibling's `ensures` reaches the verified function's query exactly like one
// in its own contracts. Its own fixture: the sibling hint widens the whole
// file's analysis, as sibling spec bodies already do.
const MONO_CALLEE: &str = r#"
use trust_vc_types::int;

enum GList<T> {
    GNil,
    GCons(T, Box<GList<T>>),
}

#[trust_vc::spec]
fn gop<T>(xs: GList<T>) -> int;

#[trust_vc::external_body]
#[trust_vc::ensures(gop::<u8>(GList::GNil) == 1)]
fn pin_gop_u8() {}

#[trust_vc::ensures(true)]
fn l27_turbofish_hidden_in_callee_ensures() {
    let a = GList::GCons(1i32, Box::new(GList::GNil));
    pin_gop_u8();
    trust_vc::assert!(gop::<i32>(GList::GNil) == 1);
}
"#;

#[test]
fn turbofish_disagreeing_with_the_monomorphized_carrier_is_refused() {
    let mut pins = Pins::default();
    pins.refused(
        verify("mono", "l26_turbofish_hidden_instantiation", MONO),
        "gop",
    );
    pins.refused(
        verify("mono", "l27_turbofish_hidden_in_contract", MONO),
        "gop",
    );
    // The same hint spelled inside a multi-clause `contract(..)` attribute.
    pins.refused(
        verify(
            "mono",
            "l27_turbofish_hidden_in_multi_clause_contract",
            MONO,
        ),
        "gop",
    );
    pins.refused(
        verify("mono_body", "l28_turbofish_hidden_in_spec_body", MONO_BODY),
        "gop",
    );
    pins.refused(
        verify(
            "mono_callee",
            "l27_turbofish_hidden_in_callee_ensures",
            MONO_CALLEE,
        ),
        "gop",
    );
    pins.verified(verify(
        "mono_agree",
        "c15_turbofish_agrees_with_carrier",
        MONO_AGREE,
    ));
    pins.finish();
}

// ---------------------------------------------------------------------------
// C9 — the refusal is not blanket over non-generic bodiless spec fns.
// ---------------------------------------------------------------------------
const NONGENERIC: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn sa() -> int;

#[trust_vc::spec]
fn sb() -> int;

#[trust_vc::ensures(true)]
fn c9_distinct_nongeneric_symbols() {
    trust_vc::assert!(sa() == sb());
}

#[trust_vc::ensures(true)]
fn c9_nongeneric_congruence() {
    trust_vc::assert!(sa() == sa());
}
"#;

#[test]
fn non_generic_bodiless_spec_fns_are_unchanged() {
    let mut pins = Pins::default();
    pins.counterexample(verify(
        "nongeneric",
        "c9_distinct_nongeneric_symbols",
        NONGENERIC,
    ));
    pins.verified(verify("nongeneric", "c9_nongeneric_congruence", NONGENERIC));
    pins.finish();
}

// ---------------------------------------------------------------------------
// L29/L30 — an impl-less trait DEFAULT body calling a refused generic callee.
// The default-conformance pass registered every free callee as an opaque
// symbol keyed by name and arguments, so `tid::<u8>() == tid::<u64>()` (and
// the exec `ereq::<u8>() == ereq::<u64>()`, 1 != 8 at runtime) "established"
// `ensures(result)` and the conformance obligation came back Verified. The
// callee is now left unregistered, the body does not lower, and the obligation
// fails closed as NotProved on the conformance channel.
// ---------------------------------------------------------------------------
const DEFAULT_SPEC_CALLEE: &str = r#"
use trust_vc_types::int;

#[trust_vc::spec]
fn tid<T>() -> int;

#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result)]
    fn dm(&self) -> bool { tid::<u8>() == tid::<u64>() }
}

#[trust_vc::ensures(true)]
fn gtv<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r);
}
"#;

const DEFAULT_EXEC_CALLEE: &str = r#"
#[trust_vc::requires(true)]
fn ereq<T>() -> u64 {
    core::mem::size_of::<T>() as u64
}

#[trust_vc::trait_spec]
trait DT {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result)]
    fn dm(&self) -> bool { ereq::<u8>() == ereq::<u64>() }
}

#[trust_vc::ensures(true)]
fn gtv<T: DT>(t: T) {
    let r = t.dm();
    trust_vc::assert!(r);
}
"#;

/// Enumerate the file's trait-conformance obligations and verify each by name,
/// exactly as `cargo trust-vc check` drives the conformance channel.
fn conformance_verdicts(tmp_id: &str, src: &str) -> Vec<(String, VerifyResult)> {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!(
        "tvc_h10_carriage_conformance_{}_{}.rs",
        std::process::id(),
        tmp_id
    ));
    std::fs::write(&p, src).expect("write fixture");
    let path = p.to_str().expect("utf8 path");
    let names = trust_vc_core::list_trait_conformance_obligations(path)
        .expect("conformance obligations enumerate");
    let verdicts = names
        .into_iter()
        .map(|name| {
            let result = trust_vc_core::verify_trait_conformance_obligation(path, &name)
                .unwrap_or_else(|e| VerifyResult::Error {
                    message: e.to_string(),
                });
            eprintln!("H10 {tmp_id} conformance [{name}]: {result:?}");
            (name, result)
        })
        .collect::<Vec<_>>();
    let _ = std::fs::remove_file(&p);
    verdicts
}

#[test]
fn trait_default_body_generic_callees_fail_closed() {
    for (tmp_id, src) in [
        ("default_spec", DEFAULT_SPEC_CALLEE),
        ("default_exec", DEFAULT_EXEC_CALLEE),
    ] {
        let verdicts = conformance_verdicts(tmp_id, src);
        assert!(
            !verdicts.is_empty(),
            "{tmp_id}: the impl-less default must still be listed as a conformance obligation"
        );
        for (name, result) in verdicts {
            assert!(
                matches!(
                    &result,
                    VerifyResult::NotProved { reason, .. }
                        if reason.contains("does not lower onto the conformance surface")
                ),
                "{tmp_id}: `{name}` rests on two instantiations of a generic callee no \
                 argument carries; it must fail closed, got {result:?}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// M1..M9 — the METHOD half. A registered method call lowers to
// `uf_name(receiver, args…)` and `mc.turbofish` was read by nothing, so a
// METHOD-level generic collapsed exactly like a free function's did.
// ---------------------------------------------------------------------------

/// `#[trust_vc::trait_spec]` methods declaring a generic parameter that no value
/// parameter carries: the bound-receiver, spec-method, concrete-receiver and
/// defaulted spellings.
const METHOD_UNCARRIED: &str = r#"
struct C { n: u64 }

#[trust_vc::trait_spec]
trait Tr {
    fn k<P>(&self) -> u64;
}

#[trust_vc::trait_impl]
impl Tr for C {
    fn k<P>(&self) -> u64 {
        1u64
    }
}

#[trust_vc::trait_spec]
trait Sp {
    #[trust_vc::spec]
    fn sk<P>(&self) -> u64;
}

#[trust_vc::trait_spec]
trait Mk {
    fn mk<P>(&self) -> u64;
}

#[trust_vc::trait_spec]
trait D {
    #[trust_vc::ensures(result)]
    fn d<P>(&self) -> bool {
        true
    }
}

#[trust_vc::ensures(true)]
fn m1_bound_receiver<T: Tr>(t: T) {
    let a = t.k::<u8>();
    let b = t.k::<u64>();
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn m2_panicking_path<T: Tr>(t: T) {
    let a = t.k::<u8>();
    let b = t.k::<u64>();
    let arr = [0u8; 4];
    if a == 1u64 && b == 8u64 {
        let _x = arr[b as usize];
    }
}

#[trust_vc::ensures(true)]
fn m3_spec_trait_method<T: Sp>(t: T) {
    trust_vc::assert!(t.sk::<u8>() == t.sk::<u64>());
}

#[trust_vc::ensures(true)]
fn m4_concrete_receiver(c: C) {
    trust_vc::assert!(c.k::<u8>() == c.k::<u64>());
}

#[trust_vc::ensures(true)]
fn m5_return_only<T: Mk>(t: T) {
    trust_vc::assert!(t.mk::<u8>() == t.mk::<u64>());
}

#[trust_vc::ensures(true)]
fn m6_defaulted<T: D>(t: T) {
    trust_vc::assert!(t.d::<u8>() == t.d::<u64>());
}

#[trust_vc::ensures(true)]
fn m7_price_same_instantiation<T: Tr>(t: T) {
    let a = t.k::<u8>();
    let b = t.k::<u8>();
    trust_vc::assert!(a == b);
}
"#;

/// A method generic a value parameter DOES carry, and the ordinary non-generic
/// trait method beside it.
const METHOD_CARRIED: &str = r#"
#[trust_vc::trait_spec]
trait Own {
    #[trust_vc::ensures(true)]
    fn m<B>(&self, x: B) -> bool;
}

#[trust_vc::trait_spec]
trait N {
    #[trust_vc::ensures(result == 7u64)]
    fn n(&self) -> u64;
}

#[trust_vc::ensures(true)]
fn c1_same_instantiation<T: Own>(t: T) {
    let a = t.m::<u8>(0u8);
    let b = t.m::<u8>(0u8);
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l1_unsuffixed_literal_cross_width<T: Own>(t: T) {
    let a = t.m::<u8>(0);
    let b = t.m::<u16>(0);
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l2_typed_cross_width<T: Own>(t: T) {
    let a = t.m::<u8>(0u8);
    let b = t.m::<u16>(0u16);
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn l3_inferred_cross_width<T: Own>(t: T) {
    let a = t.m(0u8);
    let b = t.m(0u16);
    trust_vc::assert!(a == b);
}

#[trust_vc::ensures(true)]
fn c2_non_generic_method_verifies<T: N>(t: T) {
    trust_vc::assert!(t.n() == 7u64);
}

#[trust_vc::ensures(true)]
fn l4_non_generic_method_liar<T: N>(t: T) {
    trust_vc::assert!(t.n() == 8u64);
}
"#;

/// M1..M6: a method-level generic parameter no argument carries fails EVERY
/// call closed — with a turbofish or without one, on a bound receiver, a
/// concrete `#[trust_vc::trait_impl]` receiver, a `#[trust_vc::spec]` trait
/// method and a defaulted one.
///
/// MEASURED before this refusal (cache off):
/// `m1_bound_receiver`, `m2_panicking_path`, `m3_spec_trait_method`,
/// `m4_concrete_receiver` and `m5_return_only` all returned `Verified`. The
/// runtime witness for `m1`/`m2` is `impl Tr for C { fn k<P>(&self) -> u64 {
/// size_of::<P>() as u64 } }`: it prints `a=1 b=8`, so `a == b` is FALSE and
/// `arr[b as usize]` on a `[u8; 4]` panics on the path `m2` proved unreachable.
#[test]
fn method_level_generic_instantiations_are_refused() {
    let mut pins = Pins::default();
    for (func, callee) in [
        ("m1_bound_receiver", "k"),
        ("m2_panicking_path", "k"),
        ("m3_spec_trait_method", "sk"),
        ("m4_concrete_receiver", "k"),
        ("m5_return_only", "mk"),
        ("m6_defaulted", "d"),
    ] {
        pins.refused(verify("method_uncarried", func, METHOD_UNCARRIED), callee);
    }
    // The PRICE, pinned so re-admission is deliberate: without a
    // per-instantiation symbol the method cannot be used even at ONE
    // instantiation, so a claim that is TRUE in Rust is an Error too.
    pins.refused(
        verify(
            "method_uncarried",
            "m7_price_same_instantiation",
            METHOD_UNCARRIED,
        ),
        "k",
    );
    pins.finish();
}

/// The refusal is NOT blanket: a method generic a value parameter carries still
/// lowers, while every cross-instantiation spelling — including the unsuffixed
/// literal that used to box both calls as `i32` — is REFUTED, and the ordinary
/// non-generic trait method is untouched in both directions. `c1` evaluates
/// the same generic method twice, so the repeated-call rule refuses its
/// `Verified` answer (a stateful impl can return two values); it is pinned to
/// that refusal, never to `Verified`.
///
/// MEASURED before this fix: `l1_unsuffixed_literal_cross_width` returned
/// `Verified` (a false verify this branch's free-function half did not reach).
#[test]
fn method_carried_generic_keeps_its_power_and_refutes_its_liars() {
    let mut pins = Pins::default();
    let c1 = verify("method_carried", "c1_same_instantiation", METHOD_CARRIED);
    if !matches!(
        &c1,
        VerifyResult::Error { message } if message.starts_with("bodiless call repeated")
    ) {
        pins.failures.push(format!(
            "expected the repeated-call refusal for `c1_same_instantiation`, got {c1:?}"
        ));
    }
    pins.verified(verify(
        "method_carried",
        "c2_non_generic_method_verifies",
        METHOD_CARRIED,
    ));
    pins.counterexample(verify(
        "method_carried",
        "l1_unsuffixed_literal_cross_width",
        METHOD_CARRIED,
    ));
    pins.counterexample(verify(
        "method_carried",
        "l2_typed_cross_width",
        METHOD_CARRIED,
    ));
    pins.counterexample(verify(
        "method_carried",
        "l3_inferred_cross_width",
        METHOD_CARRIED,
    ));
    pins.counterexample(verify(
        "method_carried",
        "l4_non_generic_method_liar",
        METHOD_CARRIED,
    ));
    pins.finish();
}
