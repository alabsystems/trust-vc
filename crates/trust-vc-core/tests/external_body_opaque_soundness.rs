// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! H14 — a `#[trust_vc::external_body]` / `#[trust_vc::external]` callee's BODY
//! was published as a definitional axiom, so a caller could prove facts that
//! follow only from a PLACEHOLDER.
//!
//! ## The rule
//!
//! Trust compiles the whole program together, so an ORDINARY exec callee's body
//! IS legitimately visible to its caller: definitional exec bodies are the
//! superior default here and STAY (see the capability pins at the end, each of
//! which goes red if the fix degenerates into "never publish a body axiom").
//!
//! An `external_body` / `external` function is the one exception in EVERY mode.
//! Its body is a stub: the real implementation is foreign, or elsewhere, and the
//! text in the braces is a placeholder that exists only so the item compiles.
//! Its `#[requires]`/`#[ensures]` is the whole of what it promises — that is
//! what a declared contract is for — and its body must never be a fact source.
//!
//! ## The breach, measured on `5bd3a2cc`
//!
//! FIVE publishers read the callee's body without ever consulting the attribute
//! set (`KNOWN_TRUST_VC_ATTRIBUTES` lists both names at
//! `vc_extraction/attr_extract.rs:741`):
//!
//! * `SiblingHelperDef::from_item_fn_with_name` → `__body_axiom_<f>_sibling_helper`
//!   (free functions) — E1, E2;
//! * `InherentMethodDef::apply_to_context` → `__body_axiom_<f>_inherent_method`
//!   (inherent methods) — E3, and E5 for the marker written on the IMPL BLOCK,
//!   which no publisher looked at;
//! * `register_exec_callee_postcondition_axioms` →
//!   `__body_axiom_<f>_exec_postcond_<i>` (a free exec callee of a trait default
//!   body) — E4;
//! * `SpecFunctionDef` in the spec catalog → `__body_axiom_<f>_source_catalog`
//!   (a spec fn carrying the marker, i.e. the uninterpreted-spec idiom) — E6;
//! * `register_callee_body_definition_axiom` → `__body_axiom_<f>_spec_definition`,
//!   whose `helper_body_is_visible` gate knew `opaque` and `uninterp` and not
//!   these — E6.
//!
//! So `#[trust_vc::external_body] fn eb() -> S { S { u: 100 } }` let a caller
//! prove `eb().u == 100` from the stub, and a CONTRACTED external body leaked
//! its stub value (`7`) alongside the `100` its `#[ensures]` actually promises —
//! two contradictory "facts" from one trusted declaration.
//!
//! ## The pins
//!
//! Every stub-fact witness below is paired, in the SAME fixture, with a
//! contract-path twin that must still VERIFY (the contract is not what was
//! withdrawn) and with an ordinary-exec twin that must still VERIFY (the
//! definitional-body capability is not what was withdrawn).

use std::sync::atomic::{AtomicUsize, Ordering};

use trust_vc_core::VerifyResult;

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn verdict(fixture: &str, src: &str, func: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = format!(
        "{}/external_body_opaque_{}_{fixture}_{seq}.rs",
        env!("CARGO_TARGET_TMPDIR"),
        std::process::id()
    );
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_from(&path, func);
    let _ = std::fs::remove_file(&path);
    result
}

fn verify_from(path: &str, func: &str) -> VerifyResult {
    trust_vc_core::verify_function_from_file(path, func).unwrap_or_else(|err| VerifyResult::Error {
        message: format!("{err:?}"),
    })
}

/// The trait-default channel: enumerate every conformance obligation and verify
/// each by name, exactly as `cargo trust-vc check` drives it.
fn conformance_verdict(fixture: &str, src: &str) -> VerifyResult {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::SeqCst);
    let path = format!(
        "{}/external_body_opaque_conf_{}_{fixture}_{seq}.rs",
        env!("CARGO_TARGET_TMPDIR"),
        std::process::id()
    );
    std::fs::write(&path, src).expect("write fixture");
    let result = match trust_vc_core::list_trait_conformance_obligations(&path) {
        Ok(names) => {
            assert!(
                !names.is_empty(),
                "fixture declares no conformance obligation at all — the guard would be vacuous"
            );
            let mut verdict = VerifyResult::Verified;
            for name in names {
                match trust_vc_core::verify_trait_conformance_obligation(&path, &name) {
                    Ok(result) if result.is_verified() => {}
                    Ok(result) => {
                        verdict = result;
                        break;
                    }
                    Err(err) => {
                        verdict = VerifyResult::Error {
                            message: err.to_string(),
                        };
                        break;
                    }
                }
            }
            verdict
        }
        Err(err) => VerifyResult::Error {
            message: err.to_string(),
        },
    };
    let _ = std::fs::remove_file(&path);
    result
}

/// A stub fact must not be provable — and STRICTLY: only a real refutation
/// counts, so an extraction `Error` (which would mean the target stopped being
/// extracted for some unrelated reason) cannot pass for the closed hole. Every
/// witness below was measured as a `Counterexample` whose model shows the callee
/// taking a value its stub body forbids.
fn assert_not_verified(fixture: &str, src: &str, func: &str, why: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "TRUST-BOUNDARY BREACH ({fixture}::{func}): {why}. Expected a Counterexample \
         (the stub's value is not a fact, so the claim is false of the opaque callee). Got {v:?}"
    );
}

fn assert_verified(fixture: &str, src: &str, func: &str, why: &str) {
    let v = verdict(fixture, src, func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "CAPABILITY LOST ({fixture}::{func}): {why}. Got {v:?}"
    );
}

// ===========================================================================
// E1 — a free `external_body` function.
// ===========================================================================

const E1_FREE: &str = r#"
struct S { u: u32 }

#[trust_vc::external_body]
fn eb() -> S { S { u: 100u32 } }

#[trust_vc::external_body]
#[trust_vc::ensures(result.u == 100u32)]
fn ebc() -> S { S { u: 7u32 } }

fn plain() -> S { S { u: 100u32 } }

#[trust_vc::ensures(result)]
fn e1_stub_value_is_provable() -> bool { eb().u == 100u32 }

#[trust_vc::ensures(result)]
fn e1_contract_value_is_provable() -> bool { ebc().u == 100u32 }

#[trust_vc::ensures(result)]
fn e1_stub_value_behind_contract_is_provable() -> bool { ebc().u == 7u32 }

#[trust_vc::ensures(result)]
fn e1_ordinary_body_value_is_provable() -> bool { plain().u == 100u32 }
"#;

/// THE REPRODUCER. `eb` has no contract at all, so a caller has NOTHING to go
/// on; before the fix the stub body supplied `eb().u == 100`.
#[test]
fn e1_contract_less_external_body_supplies_no_fact() {
    assert_not_verified(
        "e1",
        E1_FREE,
        "e1_stub_value_is_provable",
        "`eb` is `#[trust_vc::external_body]` and declares NO contract, so nothing is known \
         about its result; proving `eb().u == 100` can only have come from the placeholder body",
    );
}

/// THE LIAR TWIN. The same fixture, the same trusted-declaration shape — but the
/// fact asked for is the one the `#[ensures]` actually promises. Withdrawing the
/// body must not withdraw the contract.
#[test]
fn e1_external_body_contract_is_still_a_fact_source() {
    assert_verified(
        "e1",
        E1_FREE,
        "e1_contract_value_is_provable",
        "`ebc` PROMISES `result.u == 100` in its `#[ensures]`; a declared contract is exactly \
         what an external body is trusted for and must stay usable",
    );
}

/// The two halves separated: `ebc`'s stub says 7, its contract says 100. Only
/// the contract may be visible, so the stub's value must be refuted.
#[test]
fn e1_external_body_stub_behind_a_contract_supplies_no_fact() {
    assert_not_verified(
        "e1",
        E1_FREE,
        "e1_stub_value_behind_contract_is_provable",
        "`ebc`'s placeholder body returns 7 while its `#[ensures]` promises 100; proving the \
         7 means the stub body is still being read as a definition",
    );
}

/// THE OWNER RULING, pinned. Trust compiles the whole program together, so an
/// ordinary exec callee's body IS visible. This must NOT regress.
#[test]
fn e1_ordinary_exec_body_stays_definitional() {
    assert_verified(
        "e1",
        E1_FREE,
        "e1_ordinary_body_value_is_provable",
        "`plain` is an ordinary exec fn under unified compilation; its body is legitimately \
         visible to its caller and definitional exec bodies STAY",
    );
}

// ===========================================================================
// E2 — `#[trust_vc::external]` (the other trusted marker).
// ===========================================================================

const E2_EXTERNAL: &str = r#"
struct S { u: u32 }

#[trust_vc::external]
fn ex() -> S { S { u: 100u32 } }

fn plain2() -> S { S { u: 100u32 } }

#[trust_vc::ensures(result)]
fn e2_stub_value_is_provable() -> bool { ex().u == 100u32 }

#[trust_vc::ensures(result)]
fn e2_ordinary_body_value_is_provable() -> bool { plain2().u == 100u32 }
"#;

#[test]
fn e2_external_supplies_no_fact() {
    assert_not_verified(
        "e2",
        E2_EXTERNAL,
        "e2_stub_value_is_provable",
        "`ex` is `#[trust_vc::external]` — outside verification altogether — so its body text \
         is not a fact source either",
    );
}

#[test]
fn e2_ordinary_exec_body_stays_definitional() {
    assert_verified(
        "e2",
        E2_EXTERNAL,
        "e2_ordinary_body_value_is_provable",
        "the `external` refusal must be keyed to the attribute, not applied to every sibling",
    );
}

// ===========================================================================
// E3 — inherent methods (`__body_axiom_*_inherent_method`).
// ===========================================================================

const E3_INHERENT: &str = r#"
struct T { v: u32 }

impl T {
    #[trust_vc::external_body]
    fn ebm(&self) -> u32 { 100u32 }

    #[trust_vc::external_body]
    #[trust_vc::ensures(result == 100u32)]
    fn ebmc(&self) -> u32 { 7u32 }

    fn plainm(&self) -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e3_stub_value_is_provable(t: T) -> bool { t.ebm() == 100u32 }

#[trust_vc::ensures(result)]
fn e3_stub_value_behind_contract_is_provable(t: T) -> bool { t.ebmc() == 7u32 }

#[trust_vc::ensures(result)]
fn e3_ordinary_body_value_is_provable(t: T) -> bool { t.plainm() == 100u32 }
"#;

#[test]
fn e3_external_body_inherent_method_supplies_no_fact() {
    assert_not_verified(
        "e3",
        E3_INHERENT,
        "e3_stub_value_is_provable",
        "`T::ebm` is an `#[trust_vc::external_body]` inherent method with no contract; \
         `__body_axiom_T__ebm_inherent_method` published its placeholder body",
    );
}

#[test]
fn e3_external_body_inherent_method_stub_behind_contract_supplies_no_fact() {
    assert_not_verified(
        "e3",
        E3_INHERENT,
        "e3_stub_value_behind_contract_is_provable",
        "`T::ebmc`'s placeholder returns 7 while its `#[ensures]` promises 100",
    );
}

#[test]
fn e3_ordinary_inherent_method_body_stays_definitional() {
    assert_verified(
        "e3",
        E3_INHERENT,
        "e3_ordinary_body_value_is_provable",
        "an ordinary inherent method keeps its definitional body axiom",
    );
}

// ===========================================================================
// E4 — a free exec callee of a trait DEFAULT body
// (`register_exec_callee_postcondition_axioms`, trait_contracts.rs).
// ===========================================================================

const E4_TRAIT_DEFAULT_EXTERNAL: &str = r#"
#[trust_vc::external_body]
#[trust_vc::ensures(result == 7u32)]
fn ebt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { ebt() }
}
"#;

const E4_TRAIT_DEFAULT_ORDINARY: &str = r#"
#[trust_vc::ensures(result == 7u32)]
fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { okt() }
}
"#;

#[test]
fn e4_external_body_callee_does_not_discharge_a_trait_default() {
    let result = conformance_verdict("e4_ext", E4_TRAIT_DEFAULT_EXTERNAL);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "TRUST-BOUNDARY BREACH: the default `dm() {{ ebt() }}` was discharged by an axiom \
         published only because `ebt`'s PLACEHOLDER body happens to render as its \
         postcondition's rhs. An external body is not a justification. Got {result:?}"
    );
}

/// The paired capability: the identical shape with an ordinary exec callee must
/// still discharge, so the refusal is keyed to the attribute and not to the
/// publish site.
#[test]
fn e4_ordinary_callee_still_discharges_a_trait_default() {
    let result = conformance_verdict("e4_ok", E4_TRAIT_DEFAULT_ORDINARY);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST: `okt`'s body IS its postcondition's rhs, so the body-justified axiom \
         must still be published for an ordinary exec callee. Got {result:?}"
    );
}

// ===========================================================================
// E5 — the marker on the IMPL BLOCK, not on the method.
//
// `#[trust_vc::external_body] impl T { .. }` covers every method it holds, and
// measured on `5bd3a2cc` it covered none of them: `T__m(self) == 100` was
// published from the stub and a caller proved `t.m() == 100`.
//
// The same fixture declares an ORDINARY `impl V` with a method of the SAME NAME
// `m`, which must keep its body axiom — that is what pins the gate to the impl
// it is written on instead of to the method name.
// ===========================================================================

const E5_IMPL_LEVEL: &str = r#"
struct T { v: u32 }
#[trust_vc::external_body]
impl T {
    fn m(&self) -> u32 { 100u32 }
}

struct U { v: u32 }
#[trust_vc::external]
impl U {
    fn m(&self) -> u32 { 100u32 }
}

struct V { v: u32 }
impl V {
    fn m(&self) -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e5_external_body_impl_stub_is_provable(t: T) -> bool { t.m() == 100u32 }

#[trust_vc::ensures(result)]
fn e5_external_impl_stub_is_provable(u: U) -> bool { u.m() == 100u32 }

#[trust_vc::ensures(result)]
fn e5_ordinary_impl_body_is_provable(v: V) -> bool { v.m() == 100u32 }
"#;

#[test]
fn e5_external_body_on_the_impl_block_supplies_no_fact() {
    assert_not_verified(
        "e5",
        E5_IMPL_LEVEL,
        "e5_external_body_impl_stub_is_provable",
        "`impl T` carries `#[trust_vc::external_body]`, so every method it holds is a \
         placeholder; the marker is legal on the block and the publisher read only the \
         METHOD's attributes",
    );
}

#[test]
fn e5_external_on_the_impl_block_supplies_no_fact() {
    assert_not_verified(
        "e5",
        E5_IMPL_LEVEL,
        "e5_external_impl_stub_is_provable",
        "`impl U` carries `#[trust_vc::external]`",
    );
}

/// The narrowness pin: `V::m` has the SAME method name as the two stubbed ones
/// and must keep its definitional body axiom, so the gate is keyed to the impl
/// the marker is written on and not to the name.
#[test]
fn e5_ordinary_impl_with_a_colliding_method_name_stays_definitional() {
    assert_verified(
        "e5",
        E5_IMPL_LEVEL,
        "e5_ordinary_impl_body_is_provable",
        "`impl V` carries no marker; a same-named method in a marked impl elsewhere in the \
         file must not cost it its body axiom",
    );
}

// ===========================================================================
// E6 — a SPEC function carrying the marker.
//
// `#[trust_vc::spec] #[trust_vc::external_body] fn sp() -> u32 { 100 }` is the
// uninterpreted-spec-function idiom: the source declares a MEANING (its contract
// and its type), not a definition. Measured on `5bd3a2cc`, both spec publishers
// read the stub anyway — the catalog's defining axiom
// (`__body_axiom_sp_source_catalog`) and the trait-default callee lane
// (`register_callee_body_definition_axiom` → `__body_axiom_*_spec_definition`,
// whose `helper_body_is_visible` gate knew `opaque` and `uninterp` and not these).
// ===========================================================================

const E6_SPEC: &str = r#"
#[trust_vc::spec]
#[trust_vc::external_body]
fn sp() -> u32 { 100u32 }

#[trust_vc::spec]
fn sp_ok() -> u32 { 100u32 }

#[trust_vc::ensures(true)]
fn e6_spec_stub_value_is_provable() {
    trust_vc::assert!(sp() == 100u32);
}

#[trust_vc::ensures(true)]
fn e6_ordinary_spec_value_is_provable() {
    trust_vc::assert!(sp_ok() == 100u32);
}
"#;

#[test]
fn e6_external_body_spec_fn_supplies_no_fact() {
    assert_not_verified(
        "e6",
        E6_SPEC,
        "e6_spec_stub_value_is_provable",
        "`sp` is an `#[trust_vc::external_body]` spec fn — the uninterpreted-spec idiom — so \
         its braces define nothing and the catalog must emit no defining axiom, exactly as \
         for `uninterp`",
    );
}

/// The narrowness pin: an ORDINARY spec fn's body is its definition and must
/// stay one.
#[test]
fn e6_ordinary_spec_fn_body_stays_definitional() {
    assert_verified(
        "e6",
        E6_SPEC,
        "e6_ordinary_spec_value_is_provable",
        "a spec function without the marker is definitional by construction",
    );
}

const E6_TRAIT_DEFAULT_SPEC_CALLEE: &str = r#"
#[trust_vc::spec]
#[trust_vc::external_body]
fn eh() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { eh() }
}
"#;

const E6_TRAIT_DEFAULT_ORDINARY_SPEC_CALLEE: &str = r#"
#[trust_vc::spec]
fn eh_ok() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { eh_ok() }
}
"#;

#[test]
fn e6_external_body_spec_callee_does_not_discharge_a_trait_default() {
    let result = conformance_verdict("e6_ext", E6_TRAIT_DEFAULT_SPEC_CALLEE);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "TRUST-BOUNDARY BREACH: the default `dm() {{ eh() }}` was discharged from the \
         PLACEHOLDER body of an external_body spec fn. Got {result:?}"
    );
}

#[test]
fn e6_ordinary_spec_callee_still_discharges_a_trait_default() {
    let result = conformance_verdict("e6_ok", E6_TRAIT_DEFAULT_ORDINARY_SPEC_CALLEE);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST: an ordinary spec callee's definition must still reach the default. \
         Got {result:?}"
    );
}

// ===========================================================================
// E7 — the marker written on a MODULE.
//
// `#[trust_vc::external]` / `#[trust_vc::external_body]` is legal on a `mod`,
// and it means exactly what it means on an `impl` block: every item the module
// encloses is a placeholder. Round-1 review measured every one of these as
// `Verified` — the module's attributes were never read by any publisher, so a
// stub inside a marked module was still a fact source. Same class as E5 (the
// marker on the impl block), one enclosing item further out.
// ===========================================================================

const E7_MOD: &str = r#"
struct T { n: u32 }

#[trust_vc::external]
mod ext {
    pub fn ex() -> u32 { 100u32 }

    #[trust_vc::ensures(result == 42u32)]
    pub fn exc() -> u32 { 7u32 }

    impl super::T {
        pub fn m(&self) -> u32 { 100u32 }
    }
}

#[trust_vc::external_body]
mod extb {
    #[trust_vc::spec]
    pub fn sp() -> u32 { 100u32 }
}

mod plain {
    pub fn ok() -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e7_module_stub_value_is_provable() -> bool { ext::ex() == 100u32 }

#[trust_vc::ensures(result)]
fn e7_module_contract_value_is_provable() -> bool { ext::exc() == 42u32 }

#[trust_vc::ensures(result)]
fn e7_module_stub_behind_contract_is_provable() -> bool { ext::exc() == 7u32 }

#[trust_vc::ensures(result)]
fn e7_module_method_stub_value_is_provable() -> bool {
    let t = T { n: 0u32 };
    t.m() == 100u32
}

#[trust_vc::ensures(result)]
fn e7_module_spec_stub_value_is_provable() -> bool { extb::sp() == 100u32 }

#[trust_vc::ensures(result)]
fn e7_plain_module_body_value_is_provable() -> bool { plain::ok() == 100u32 }
"#;

/// THE REPRODUCER (review round 1, blocker). The marker is on the module; the
/// stub body inside it was still published as `ex() == 100`.
#[test]
fn e7_external_marked_module_free_fn_supplies_no_fact() {
    assert_not_verified(
        "e7",
        E7_MOD,
        "e7_module_stub_value_is_provable",
        "`mod ext` carries `#[trust_vc::external]`, so `ex`'s braces are a PLACEHOLDER exactly \
         as if the marker sat on the function; proving `ex() == 100` can only have come from \
         that placeholder",
    );
}

/// THE LIAR TWIN. A contract declared inside a marked module is still a
/// contract.
#[test]
fn e7_external_marked_module_contract_is_still_a_fact_source() {
    assert_verified(
        "e7",
        E7_MOD,
        "e7_module_contract_value_is_provable",
        "`exc` PROMISES `result == 42`; enclosing it in an external-marked module withdraws \
         its BODY, never its declared contract",
    );
}

#[test]
fn e7_external_marked_module_stub_behind_contract_is_refuted() {
    assert_not_verified(
        "e7",
        E7_MOD,
        "e7_module_stub_behind_contract_is_provable",
        "`exc`'s stub says 7 and its contract says 42; only the contract may be visible",
    );
}

#[test]
fn e7_external_marked_module_inherent_method_supplies_no_fact() {
    assert_not_verified(
        "e7",
        E7_MOD,
        "e7_module_method_stub_value_is_provable",
        "a method on a type declared inside an external-marked module is covered by the \
         module's marker too",
    );
}

#[test]
fn e7_external_marked_module_spec_fn_supplies_no_fact() {
    assert_not_verified(
        "e7",
        E7_MOD,
        "e7_module_spec_stub_value_is_provable",
        "a `#[trust_vc::spec]` fn inside an `#[trust_vc::external_body]` module is the \
         uninterpreted-spec idiom: symbol declared, no defining axiom",
    );
}

/// NARROWNESS. An UNMARKED module keeps the definitional-body capability — the
/// owner ruling is that ordinary exec bodies stay visible under Trust's unified
/// compilation, and "inside a module" is not a marker.
#[test]
fn e7_unmarked_module_body_stays_definitional() {
    assert_verified(
        "e7",
        E7_MOD,
        "e7_plain_module_body_value_is_provable",
        "`mod plain` carries no marker at all; its callee's body is the superior default and \
         must still reach the caller",
    );
}

// ===========================================================================
// E8 — a `trust_vc::`-namespaced attribute on a MODULE was DISCARDED in
// silence, so a misspelled marker read exactly like a correct one.
// ===========================================================================

const E8_UNKNOWN_MOD_ATTR: &str = r#"
#[trust_vc::externl_body]
mod ext {
    pub fn ex() -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e8_typoed_marker_is_silently_dropped() -> bool { ext::ex() == 100u32 }
"#;

const E8_KNOWN_MOD_ATTR: &str = r#"
#[cfg(not(test))]
mod ext {
    pub fn ex() -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e8_foreign_module_attr_is_untouched() -> bool { ext::ex() == 100u32 }
"#;

const E8_LINT_MOD_ATTR: &str = r#"
#[allow(dead_code)]
mod ext {
    pub fn ex() -> u32 { 100u32 }
}

#[trust_vc::ensures(result)]
fn e8_foreign_module_attr_is_untouched() -> bool { ext::ex() == 100u32 }
"#;

#[test]
fn e8_unknown_trust_vc_module_attribute_is_refused() {
    let v = verdict(
        "e8",
        E8_UNKNOWN_MOD_ATTR,
        "e8_typoed_marker_is_silently_dropped",
    );
    let VerifyResult::Error { message } = &v else {
        panic!(
            "SILENT DROP: `#[trust_vc::externl_body]` on a module is a MISSPELLED trust \
             boundary, and dropping it verifies the caller from a placeholder body while the \
             author believes the module is opaque. Expected a refusal, got {v:?}"
        );
    };
    assert!(
        message.contains("unknown trust_vc attribute"),
        "refused, but not as an unknown-attribute boundary. Got: {message}"
    );
}

/// NARROWNESS. Only `trust_vc::`-namespaced module attributes are in scope;
/// ordinary Rust module attributes keep falling through exactly as before.
///
/// A lint attribute cannot remove the module, so the caller reads its body and
/// verifies. A `#[cfg(not(test))]` module is not refused by this rule either,
/// but the caller is refused by the `#[cfg]` rule, and that verdict is the
/// correct one: when `test` is set the module is compiled out and `ext::ex()`
/// resolves through the extern prelude to any crate named `ext` (a renamed
/// dev-dependency, the usual way to substitute a mock). With such a crate
/// returning `7`, the function compiles and returns `false` in that build, so
/// `Verified` would be a false claim about it.
#[test]
fn e8_foreign_module_attribute_still_falls_through() {
    assert_verified(
        "e8",
        E8_LINT_MOD_ATTR,
        "e8_foreign_module_attr_is_untouched",
        "`#[allow(..)]` is not a trust_vc clause; rejecting it would refuse most real files",
    );
    let v = verdict(
        "e8",
        E8_KNOWN_MOD_ATTR,
        "e8_foreign_module_attr_is_untouched",
    );
    let VerifyResult::Error { message } = &v else {
        panic!(
            "`ext` is compiled out when `test` is set, and the path then resolves outside \
             this file; expected the `#[cfg]` refusal, got {v:?}"
        );
    };
    assert!(
        !message.contains("unknown trust_vc attribute"),
        "a foreign module attribute was refused as a trust_vc attribute: {message}"
    );
    assert!(
        message.contains(
            "reaches a declaration in this file that carries a `#[cfg]` / `#[cfg_attr]` \
             attribute; vc_extraction does not evaluate `cfg`"
        ),
        "expected the `#[cfg]` refusal, got: {message}"
    );
}

// ===========================================================================
// E9 — the SIXTH publisher, in the PROC-MACRO lane. `spec_expand.rs` builds
// `__body_axiom_<f>` = `<call> == <body tokens>` and pushes it as a
// `broadcast_assume`. It detects `opaque` and `inline` by last path segment and
// knows nothing about `external` / `external_body`, so the proc-macro lane and
// the FILE lane (`spec_function_catalog`, closed by E6) DISAGREE about the same
// source text: the uninterpreted-spec idiom
// `#[trust_vc::spec] #[trust_vc::external_body] fn sp() -> u32 { 100 }`.
// ===========================================================================

fn spec_expansion(input: syn::ItemFn) -> String {
    trust_vc_core::expand_spec(input).to_string()
}

#[test]
fn e9_proc_macro_lane_publishes_no_defining_axiom_for_an_external_body_spec_fn() {
    let out = spec_expansion(syn::parse_quote! {
        #[trust_vc::external_body]
        fn sp() -> u32 { 100u32 }
    });
    assert!(
        !out.contains("__body_axiom_sp"),
        "TRUST-BOUNDARY BREACH (e9, external_body): the proc-macro lane still emits the \
         defining axiom `sp() == 100u32` for a spec fn on the trusted boundary, while the \
         file lane declines the identical source (E6). One source text, two lanes, two \
         answers. Expansion:\n{out}"
    );
}

#[test]
fn e9_proc_macro_lane_publishes_no_defining_axiom_for_an_external_spec_fn() {
    let out = spec_expansion(syn::parse_quote! {
        #[trust_vc::external]
        fn sp() -> u32 { 100u32 }
    });
    assert!(
        !out.contains("__body_axiom_sp"),
        "TRUST-BOUNDARY BREACH (e9, external): `#[trust_vc::external]` is the same boundary \
         as `external_body` for this purpose — the braces hold a placeholder. Expansion:\n{out}"
    );
}

/// The marker is deliberately matched by LAST SEGMENT, as everywhere else on
/// this boundary, so a foreign namespace spelling declines too.
#[test]
fn e9_proc_macro_lane_declines_a_foreign_namespace_spelling() {
    let out = spec_expansion(syn::parse_quote! {
        #[verifier::external_body]
        fn sp() -> u32 { 100u32 }
    });
    assert!(
        !out.contains("__body_axiom_sp"),
        "TRUST-BOUNDARY BREACH (e9, foreign namespace): last-segment matching is what every \
         other publisher on this boundary uses. Expansion:\n{out}"
    );
}

/// NARROWNESS, and the owner ruling in the proc-macro lane: an ORDINARY spec
/// function's body is its DEFINITION and must still be published. Without this
/// pin the fix above could degenerate into "never publish a body axiom".
#[test]
fn e9_ordinary_spec_fn_still_publishes_its_defining_axiom() {
    let out = spec_expansion(syn::parse_quote! {
        fn sp() -> u32 { 100u32 }
    });
    assert!(
        out.contains("__body_axiom_sp"),
        "CAPABILITY LOST (e9): an unmarked `#[trust_vc::spec]` function is DEFINED by its \
         body; withdrawing that axiom would break every spec function. Expansion:\n{out}"
    );
}

// ===========================================================================
// E10 — OVER-REJECTION introduced by the E7 fix. `external_marked_module_
// declares_name` matched on the BARE NAME only, with no module-path or scope
// check, so ONE marked module declaring a common name (`new`, `val`,
// `shared_name`) silently stripped the definitional body axiom from EVERY
// unrelated same-named function in the file. Under the owner's unified-
// compilation ruling that is a real capability loss, not a safe over-decline.
// ===========================================================================

const E10_FREE_FN_NAME_COLLISION: &str = r#"
#[trust_vc::external]
mod ext {
    pub fn shared_name() -> u32 { 100u32 }
}

fn shared_name() -> u32 { 7u32 }

#[trust_vc::ensures(result)]
fn e10_unrelated_same_name_value_is_provable() -> bool { shared_name() == 7u32 }

#[trust_vc::ensures(result)]
fn e10_marked_module_stub_value_is_provable() -> bool { ext::shared_name() == 100u32 }
"#;

#[test]
fn e10_unrelated_free_fn_keeps_its_definitional_body() {
    assert_verified(
        "e10",
        E10_FREE_FN_NAME_COLLISION,
        "e10_unrelated_same_name_value_is_provable",
        "the top-level `shared_name` is an ORDINARY exec function that merely SHARES A NAME \
         with one inside an external-marked module; Trust compiles the whole program \
         together, so its body is legitimately visible to its caller and must stay a fact \
         source",
    );
}

#[test]
fn e10_marked_module_fn_still_supplies_no_fact() {
    assert_not_verified(
        "e10",
        E10_FREE_FN_NAME_COLLISION,
        "e10_marked_module_stub_value_is_provable",
        "scoping the marker to the declarations it actually covers must not reopen E7: the \
         module-enclosed `shared_name` is still a placeholder",
    );
}

const E10_METHOD_NAME_COLLISION: &str = r#"
struct P {
    n: u32,
}

#[trust_vc::external_body]
mod ext {
    impl super::P {
        pub fn val(&self) -> u32 { 100u32 }
    }
}

struct Q {
    n: u32,
}

impl Q {
    fn val(&self) -> u32 { 7u32 }
}

#[trust_vc::ensures(result)]
fn e10_unrelated_method_value_is_provable() -> bool {
    let q = Q { n: 0u32 };
    q.val() == 7u32
}

#[trust_vc::ensures(result)]
fn e10_marked_module_method_stub_value_is_provable() -> bool {
    let p = P { n: 0u32 };
    p.val() == 100u32
}
"#;

#[test]
fn e10_unrelated_inherent_method_keeps_its_definitional_body() {
    assert_verified(
        "e10",
        E10_METHOD_NAME_COLLISION,
        "e10_unrelated_method_value_is_provable",
        "`Q::val` has nothing to do with `ext::P::val`; a marked module declaring a common \
         method name (`new`, `val`, `len`) must not strip the body axiom off every unrelated \
         method of that name in the file",
    );
}

#[test]
fn e10_marked_module_method_still_supplies_no_fact() {
    assert_not_verified(
        "e10",
        E10_METHOD_NAME_COLLISION,
        "e10_marked_module_method_stub_value_is_provable",
        "the SAME file now holds a marked `ext::P::val` and an unrelated `Q::val`; narrowing \
         the marker to the declarations it covers must keep `ext::P::val` a placeholder",
    );
}

const E10_TRAIT_DEFAULT_NAME_COLLISION: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::ensures(result == 9u32)]
    pub fn okt() -> u32 { 9u32 }
}

#[trust_vc::ensures(result == 7u32)]
fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { okt() }
}
"#;

/// The callee is spelled `crate::eh_ok` DELIBERATELY. A bare `eh_ok()` here
/// routes through `SpecFunctionCatalog`, which keys nested `pub` spec fns by
/// their BARE NAME as well as their qualified path, so the module's `eh_ok`
/// displaces the top-level one before any marker is consulted — measured on this
/// branch with the module UNMARKED and still `Counterexample`. That is a
/// separate, PRE-EXISTING bare-name collision in the catalog lane (recorded as a
/// residual), and pinning it here would measure that instead of this fix. The
/// `crate::`-prefixed spelling routes to `register_callee_body_definition_axiom`
/// and its `helper_body_is_visible` gate, which is the site under test.
const E10_TRAIT_DEFAULT_SPEC_CALLEE_COLLISION: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::spec]
    pub fn eh_ok() -> u32 { 9u32 }
}

#[trust_vc::spec]
fn eh_ok() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { crate::eh_ok() }
}
"#;

/// The REFUTED liars for the two conformance pins below. Same text, opposite
/// claim: the trait default's `ensures` now names the value the MARKED module's
/// declaration would supply (9), which the top-level one never returns. A
/// Counterexample here is what shows the verified twins are discharged from the
/// TOP-LEVEL body and not from an obligation channel that has gone quiet.
const E10_TRAIT_DEFAULT_NAME_COLLISION_LIAR: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::ensures(result == 9u32)]
    pub fn okt() -> u32 { 9u32 }
}

#[trust_vc::ensures(result == 7u32)]
fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 9u32)]
    fn dm(&self) -> u32 { okt() }
}
"#;

const E10_TRAIT_DEFAULT_SPEC_CALLEE_COLLISION_LIAR: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::spec]
    pub fn eh_ok() -> u32 { 9u32 }
}

#[trust_vc::spec]
fn eh_ok() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 9u32)]
    fn dm(&self) -> u32 { crate::eh_ok() }
}
"#;

#[test]
fn e10_trait_default_spec_callee_liar_is_refuted() {
    let result = conformance_verdict(
        "e10_conf_spec_liar",
        E10_TRAIT_DEFAULT_SPEC_CALLEE_COLLISION_LIAR,
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "(e10 conformance, spec callee liar) the TOP-LEVEL `eh_ok` returns 100, so an \
         `ensures(result == 9u32)` default body must be REFUTED — 9 is the marked module's \
         value and is not a fact. Got {result:?}"
    );
}

#[test]
fn e10_trait_default_callee_liar_is_refuted() {
    let result = conformance_verdict("e10_conf_liar", E10_TRAIT_DEFAULT_NAME_COLLISION_LIAR);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "(e10 conformance liar) the TOP-LEVEL `okt` returns 7, so an \
         `ensures(result == 9u32)` default body must be REFUTED. Got {result:?}"
    );
}

/// The fourth name-matched site, `helper_body_is_visible`
/// (`trait_contracts.rs`). Same over-rejection, same fix: measured
/// `Counterexample` with the round-1 bare-name predicate restored in place, and
/// `Verified` with the identity-scoped one.
#[test]
fn e10_trait_default_keeps_an_unrelated_spec_callee_body() {
    let result = conformance_verdict("e10_conf_spec", E10_TRAIT_DEFAULT_SPEC_CALLEE_COLLISION);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST (e10 conformance, spec callee): the default body calls the \
         TOP-LEVEL `eh_ok`, an ordinary spec function whose body IS its definition. Got \
         {result:?}"
    );
}

/// The trait-default channel has TWO of the four name-matched sites
/// (`helper_body_is_visible` and `register_exec_callee_postcondition_axioms`), so
/// the over-rejection reached it too: the default body's callee is the TOP-LEVEL
/// `shared_name`, and the marked module merely reuses the name.
#[test]
fn e10_trait_default_keeps_an_unrelated_callee_body() {
    let result = conformance_verdict("e10_conf", E10_TRAIT_DEFAULT_NAME_COLLISION);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST (e10 conformance): the default body calls the TOP-LEVEL \
         `shared_name`, whose body is an ordinary visible definition; a marked module that \
         happens to declare the same name must not withdraw it. Got {result:?}"
    );
}

// ===========================================================================
// E11 — the EIGHTH publisher, and the last one on this boundary inside
// trust-vc-core: the TRAIT-DEFAULT-BODY lane. `TraitMethodDecl.default_body`
// (built in `trait_expand::parse_trait_method_decl` from `method.default`) is
// published as the defining equation `Trait__m(self) == <default body>` by
// `encoder/trait_encoding.rs` -> `trait_encoding_axioms::assert_default_body_
// axiom`. Nothing on that path read `has_external_trusted_attr` — not on the
// METHOD, not on the TRAIT, not on the ENCLOSING MODULE — so a contract-free
// `#[trust_vc::external_body]` trait default published its STUB as a fact and a
// caller proved it. That is the E1/E7 breach one item further out, and the
// module case defeated the round-1 claim that a marker on a MODULE opaques
// every body inside it.
//
// Only the CONTRACTED variant was safe, and only by accident: `trait_encoding`
// already skips a default whose `ensures` is non-empty ("CONTRACT WINS").
//
// Measured identically at the merge base and on this branch, so PRE-EXISTING,
// not a regression of this branch — but H14 cannot be called closed while it
// stands.
// ===========================================================================

const E11_METHOD_MARKER: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::external_body]
    fn m(&self) -> u32 { 100u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_method_marker_stub_value_is_provable(a: A) -> bool { a.m() == 100u32 }
"#;

const E11_TRAIT_MARKER: &str = r#"
#[trust_vc::external_body]
#[trust_vc::trait_spec]
trait Tr {
    fn m(&self) -> u32 { 100u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_trait_marker_stub_value_is_provable(a: A) -> bool { a.m() == 100u32 }
"#;

const E11_MODULE_MARKER: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::trait_spec]
    pub trait Tr {
        fn m(&self) -> u32 { 100u32 }
    }

    pub struct A;

    #[trust_vc::trait_impl(Tr)]
    impl Tr for A {}
}

use ext::Tr;

#[trust_vc::ensures(result)]
fn e11_module_marker_stub_value_is_provable(a: ext::A) -> bool { a.m() == 100u32 }
"#;

const E11_EXTERNAL_SPELLING: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::external]
    fn m(&self) -> u32 { 100u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_external_spelling_stub_value_is_provable(a: A) -> bool { a.m() == 100u32 }
"#;

const E11_FOREIGN_NAMESPACE: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[verifier::external_body]
    fn m(&self) -> u32 { 100u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_foreign_namespace_stub_value_is_provable(a: A) -> bool { a.m() == 100u32 }
"#;

/// NARROWNESS / the owner's unified-compilation ruling in this lane: an
/// UNMARKED trait default body IS its definition and must stay a fact source.
/// Without this pin the fix could degenerate into "never publish a trait default
/// body axiom", which would withdraw a real capability.
const E11_ORDINARY_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    fn m(&self) -> u32 { 100u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_ordinary_default_value_is_provable(a: A) -> bool { a.m() == 100u32 }

#[trust_vc::ensures(result)]
fn e11_ordinary_default_liar(a: A) -> bool { a.m() == 101u32 }
"#;

/// A marked default that DOES carry a contract still publishes that contract —
/// the contract is what a trusted declaration promises. The stub value (7) must
/// stay unprovable; the promised value (100) must stay provable.
const E11_CONTRACTED: &str = r#"
#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::external_body]
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn m(&self) -> u32 { 7u32 }
}

struct A;

#[trust_vc::trait_impl(Tr)]
impl Tr for A {}

#[trust_vc::ensures(result)]
fn e11_contract_value_is_provable(a: A) -> bool { a.m() == 100u32 }

#[trust_vc::ensures(result)]
fn e11_contracted_stub_value_is_provable(a: A) -> bool { a.m() == 7u32 }
"#;

#[test]
fn e11_trait_default_with_a_method_marker_supplies_no_fact() {
    assert_not_verified(
        "e11",
        E11_METHOD_MARKER,
        "e11_method_marker_stub_value_is_provable",
        "the default body of an `#[trust_vc::external_body]` trait method is a PLACEHOLDER; \
         publishing `Tr__m(self) == 100` hands a caller a fact the real implementation never \
         promised",
    );
}

#[test]
fn e11_trait_default_with_a_trait_marker_supplies_no_fact() {
    assert_not_verified(
        "e11",
        E11_TRAIT_MARKER,
        "e11_trait_marker_stub_value_is_provable",
        "the marker is legal on the TRAIT, where it covers every method the trait declares, \
         exactly as it does on an `impl` block and on a `mod`",
    );
}

#[test]
fn e11_trait_default_inside_a_marked_module_supplies_no_fact() {
    assert_not_verified(
        "e11",
        E11_MODULE_MARKER,
        "e11_module_marker_stub_value_is_provable",
        "round 1 claimed a marker on a MODULE opaques every body inside it; a trait default \
         body inside that module is one of those bodies",
    );
}

#[test]
fn e11_trait_default_external_spelling_supplies_no_fact() {
    assert_not_verified(
        "e11",
        E11_EXTERNAL_SPELLING,
        "e11_external_spelling_stub_value_is_provable",
        "`#[trust_vc::external]` is the same trust boundary as `external_body` here",
    );
}

#[test]
fn e11_trait_default_foreign_namespace_supplies_no_fact() {
    assert_not_verified(
        "e11",
        E11_FOREIGN_NAMESPACE,
        "e11_foreign_namespace_stub_value_is_provable",
        "last-segment matching is what every other publisher on this boundary uses, so \
         `#[verifier::external_body]` declines too",
    );
}

#[test]
fn e11_ordinary_trait_default_keeps_its_definitional_body() {
    assert_verified(
        "e11",
        E11_ORDINARY_DEFAULT,
        "e11_ordinary_default_value_is_provable",
        "an UNMARKED trait default body is its definition; Trust compiles the whole program \
         together and the inherited default IS the code that runs",
    );
}

/// The liar for the pin above — every verified pin in this suite carries one.
/// It is checked and not proved: were the context contradictory, the liar
/// would verify alongside its twin.
///
/// It is the one pin here that accepts `unknown` as well as a counterexample.
/// The default body axiom speaks only of the impl's own receivers
/// (`∀s:A. Tr__m(Box_A(s)) == 100`), and ay's model gate commits no value for
/// `Box_A` under that quantifier, so ay answers `unknown` where the axiom over
/// every receiver let it answer `sat`. That axiom was false for an impl that
/// overrides the default (`trait_default_override_soundness`).
#[test]
fn e11_ordinary_trait_default_does_not_prove_the_negation() {
    let v = verdict("e11", E11_ORDINARY_DEFAULT, "e11_ordinary_default_liar");
    assert!(
        matches!(
            v,
            VerifyResult::Counterexample { .. }
                | VerifyResult::NotProved { .. }
                | VerifyResult::Unknown { .. }
        ),
        "the unmarked default returns 100, so claiming 101 must be checked and not proved. \
         Got {v:?}"
    );
}

#[test]
fn e11_contracted_marked_default_still_publishes_its_contract() {
    assert_verified(
        "e11",
        E11_CONTRACTED,
        "e11_contract_value_is_provable",
        "withdrawing the BODY axiom must not withdraw the declared `#[ensures]`, which is \
         the whole of what a trusted declaration promises",
    );
}

#[test]
fn e11_contracted_marked_default_leaks_no_stub_value() {
    assert_not_verified(
        "e11",
        E11_CONTRACTED,
        "e11_contracted_stub_value_is_provable",
        "the stub tail (7) is not a fact even when the same declaration promises 100",
    );
}

// ===========================================================================
// E12 — the surviving half of the E10 over-rejection. `external_marked_
// boundary_covers_fn` collected EVERY token-identical declaration in the file
// and answered `.any(marked)`, so when a free fn is declared token-identically
// both INSIDE a trusted-boundary-marked module and OUTSIDE it, the unrelated
// OUTSIDE one lost its definitional body axiom too. Fail-closed, but under the
// owner's unified-compilation ruling a lost body axiom for an ORDINARY function
// is a real capability loss.
//
// The fix resolves the callee by the PATH it was actually resolved through
// (`SourceFunctionRegistry`'s inline-module key), so `ffi::len` and `len` are
// two different declarations even when their tokens agree.
// ===========================================================================

const E12_IDENTICAL_BODIES: &str = r#"
#[trust_vc::external]
mod ffi {
    pub fn len() -> u32 { 7u32 }
}

pub fn len() -> u32 { 7u32 }

#[trust_vc::ensures(result)]
fn e12_unrelated_identical_body_is_provable() -> bool { len() == 7u32 }

#[trust_vc::ensures(result)]
fn e12_marked_identical_body_is_provable() -> bool { ffi::len() == 7u32 }
"#;

#[test]
fn e12_token_identical_outside_fn_keeps_its_definitional_body() {
    assert_verified(
        "e12",
        E12_IDENTICAL_BODIES,
        "e12_unrelated_identical_body_is_provable",
        "the top-level `len` is an ORDINARY exec function that merely happens to be spelled \
         exactly like one inside a marked module; its body is legitimately visible to its \
         caller and must stay a fact source",
    );
}

#[test]
fn e12_token_identical_marked_fn_still_supplies_no_fact() {
    assert_not_verified(
        "e12",
        E12_IDENTICAL_BODIES,
        "e12_marked_identical_body_is_provable",
        "resolving the marker by PATH must not reopen E7: `ffi::len` is still a placeholder \
         even though an identical body sits at the file root",
    );
}

// ===========================================================================
// E13 — E12's fix landed in ONE of the THREE consumers of the approximate
// predicate. `external_marked_boundary_covers_fn` still collects every
// token-identical declaration in the file and answers `.any(marked)`, and the
// TRAIT-DEFAULT channel still called it RAW at both of its sites
// (`helper_body_is_visible`, `register_exec_callee_postcondition_axioms`). So
// the SAME source shape that E12 measured as `Verified` on the sibling-helper
// lane was still `Counterexample` here: one program, two lanes, two answers.
//
// E10 could not see this. Its fixtures give the two declarations DIFFERENT
// bodies (9 inside the marked module, 7 outside), which the round-2
// identity-scoped matcher already separates. The surviving hole needs them
// TOKEN-IDENTICAL — same attrs, same vis, same signature, same body — where
// identity cannot tell the two apart and only the RESOLVED PATH can.
//
// Both directions are pinned in both lanes: the top-level declaration keeps its
// definitional body, the marked module's own declaration stays opaque (E7 is
// not reopened), and a liar twin refutes so the Verified is discharged from the
// body rather than from a channel that has gone quiet.
// ===========================================================================

/// The trait-default EXEC-callee lane (`register_exec_callee_postcondition_axioms`).
const E13_EXEC_IDENTICAL: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::ensures(result == 7u32)]
    pub fn okt() -> u32 { 7u32 }
}

#[trust_vc::ensures(result == 7u32)]
pub fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { okt() }
}
"#;

/// Same two token-identical declarations; the default now calls the one INSIDE
/// the marked module. It must stay opaque.
const E13_EXEC_IDENTICAL_MARKED: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::ensures(result == 7u32)]
    pub fn okt() -> u32 { 7u32 }
}

#[trust_vc::ensures(result == 7u32)]
pub fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 7u32)]
    fn dm(&self) -> u32 { ext::okt() }
}
"#;

/// The REFUTED liar twin of `E13_EXEC_IDENTICAL`: same text, a claim the
/// top-level `okt` never satisfies.
const E13_EXEC_IDENTICAL_LIAR: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::ensures(result == 7u32)]
    pub fn okt() -> u32 { 7u32 }
}

#[trust_vc::ensures(result == 7u32)]
pub fn okt() -> u32 { 7u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 8u32)]
    fn dm(&self) -> u32 { okt() }
}
"#;

/// The trait-default SPEC-callee lane (`helper_body_is_visible`, reached through
/// `register_callee_body_definition_axiom`). The `crate::` prefix is deliberate
/// and is the same routing note E10 records: a bare spelling goes through
/// `SpecFunctionCatalog`'s bare-name keying, which is a different (pre-existing)
/// collision; the notation-prefixed spelling routes to the gate under test.
const E13_SPEC_IDENTICAL: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::spec]
    pub fn ehk() -> u32 { 100u32 }
}

#[trust_vc::spec]
pub fn ehk() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { crate::ehk() }
}
"#;

const E13_SPEC_IDENTICAL_MARKED: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::spec]
    pub fn ehk() -> u32 { 100u32 }
}

#[trust_vc::spec]
pub fn ehk() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 100u32)]
    fn dm(&self) -> u32 { crate::ext::ehk() }
}
"#;

const E13_SPEC_IDENTICAL_LIAR: &str = r#"
#[trust_vc::external_body]
mod ext {
    #[trust_vc::spec]
    pub fn ehk() -> u32 { 100u32 }
}

#[trust_vc::spec]
pub fn ehk() -> u32 { 100u32 }

#[trust_vc::trait_spec]
trait Tr {
    #[trust_vc::returns(result)]
    #[trust_vc::ensures(result == 101u32)]
    fn dm(&self) -> u32 { crate::ehk() }
}
"#;

#[test]
fn e13_trait_default_exec_callee_keeps_its_token_identical_outside_body() {
    let result = conformance_verdict("e13_exec", E13_EXEC_IDENTICAL);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST (e13, trait-default EXEC-callee lane): the default body calls the \
         TOP-LEVEL `okt`, an ordinary exec function that merely happens to be spelled exactly \
         like one inside a marked module. E12 already measured this same shape as Verified on \
         the sibling-helper lane, so a Counterexample here is the tree disagreeing with \
         itself across lanes. Got {result:?}"
    );
}

#[test]
fn e13_trait_default_exec_callee_inside_the_marked_module_stays_opaque() {
    let result = conformance_verdict("e13_exec_marked", E13_EXEC_IDENTICAL_MARKED);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "TRUST-BOUNDARY BREACH (e13, trait-default EXEC-callee lane): resolving the marker by \
         PATH must not reopen E7 — `ext::okt` is still a placeholder even though an identical \
         declaration sits at the file root. Got {result:?}"
    );
}

#[test]
fn e13_trait_default_exec_callee_liar_is_refuted() {
    let result = conformance_verdict("e13_exec_liar", E13_EXEC_IDENTICAL_LIAR);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "(e13 exec liar) the TOP-LEVEL `okt` returns 7, so an `ensures(result == 8u32)` \
         default body must be REFUTED — the verified twin is discharged from that body and \
         not from an obligation channel that has gone quiet. Got {result:?}"
    );
}

#[test]
fn e13_trait_default_spec_callee_keeps_its_token_identical_outside_body() {
    let result = conformance_verdict("e13_spec", E13_SPEC_IDENTICAL);
    assert!(
        matches!(result, VerifyResult::Verified),
        "CAPABILITY LOST (e13, trait-default SPEC-callee lane): the default body calls the \
         TOP-LEVEL `ehk`, an ordinary spec function whose body IS its definition; a marked \
         module holding a token-identical declaration must not withdraw it. Got {result:?}"
    );
}

#[test]
fn e13_trait_default_spec_callee_inside_the_marked_module_stays_opaque() {
    let result = conformance_verdict("e13_spec_marked", E13_SPEC_IDENTICAL_MARKED);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "TRUST-BOUNDARY BREACH (e13, trait-default SPEC-callee lane): `ext::ehk` carries the \
         module marker and must supply no defining axiom, even though an identical \
         declaration sits at the file root. Got {result:?}"
    );
}

#[test]
fn e13_trait_default_spec_callee_liar_is_refuted() {
    let result = conformance_verdict("e13_spec_liar", E13_SPEC_IDENTICAL_LIAR);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "(e13 spec liar) the TOP-LEVEL `ehk` is 100, so an `ensures(result == 101u32)` \
         default body must be REFUTED. Got {result:?}"
    );
}
