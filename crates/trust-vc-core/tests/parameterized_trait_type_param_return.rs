// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Parameterized-trait dispatch slice (row 382): a method whose TRAIT declares a
//! BARE type-param return (`trait Container<A> { fn get(&self) -> A; }`) that a
//! concrete impl binds (`impl Container<u64> for S { fn get(&self) -> u64 }`) now
//! resolves at a `s: S` receiver.
//!
//! WHY IT WAS UNKNOWN: the shared per-trait UF's impl-postcondition linking axiom
//! (`trait_encoding_axioms.rs`) DROPS a method whose return contains a type param
//! (the UF cannot carry the per-impl-resolved return sort), so `s.get()` stayed
//! unconstrained. The impl writes the CONCRETE return, so its definitional body
//! axiom (`S::get(self) == <body>`) carries the right sort — the same mechanism
//! the assoc-type-return and inherent paths use.
//!
//! SOUNDNESS MODEL:
//!   · The published fact is the DEFINITIONAL BODY AXIOM (the actual computation),
//!     NOT an unchecked contract — a false consequence fails closed (`liar`).
//!   · Admission is NARROW: only a bare-type-param RETURN with all-bare-or-concrete
//!     positions. A NESTED type-param (`fn f(&self, xs: Seq<A>)`) stays fail-closed
//!     (da02cb7 false-verify — covered by `trait_generic_soundness`); a CONCRETE
//!     return stays on the UF path (no double-registration).
//!   · A COLLISION GATE requires the `(self-type, method)` pair be UNIQUE across
//!     trait impls: two impls on one self-type declaring one method (`impl
//!     Container<u64> for S` + `impl Box2<u64> for S`, both `get`) would register
//!     conflicting `S::get` body axioms, and the keeps-first dedup would publish a
//!     mismatched body — a false-verify. It fails closed instead (`collision`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_pttp_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

// A trait declaring a bare type-param return, bound concretely by the impl.
const SIMPLE: &str = r#"
#[trust_vc::trait_spec]
trait Container<A> { fn get(&self) -> A; }
struct S;
#[trust_vc::trait_impl]
impl Container<u64> for S {
    #[trust_vc::ensures(result == 5u64)] fn get(&self) -> u64 { 5u64 }
}
#[trust_vc::ensures(true)]
fn pos(s: S) { trust_vc::assert!(s.get() == 5u64); }
// CARDINAL LIAR: a fixed wrong value must fail closed (also proves non-vacuity).
#[trust_vc::ensures(true)]
fn liar(s: S) { trust_vc::assert!(s.get() == 6u64); }
"#;

// A bare type-param return whose body reads a field (`self.v`), threaded through
// the concrete `impl Container<u64> for S`.
const FIELD_BODY: &str = r#"
#[trust_vc::trait_spec]
trait Container<A> { fn get(&self) -> A; }
struct S { v: u64 }
#[trust_vc::trait_impl]
impl Container<u64> for S {
    #[trust_vc::ensures(result == self.v)] fn get(&self) -> u64 { self.v }
}
#[trust_vc::ensures(true)]
fn fpos(s: S) { trust_vc::assert!(s.get() == s.v); }
#[trust_vc::requires(s.v == 7u64)]
#[trust_vc::ensures(true)]
fn fliar(s: S) { trust_vc::assert!(s.get() == 8u64); }
"#;

// A bare type-param ARGUMENT alongside the bare type-param return
// (`fn combine(&self, x: A) -> A`): the same admission path covers it (return is
// bare `A`, the `x: A` param instantiates to concrete `u64`).
const ARG_AND_RETURN: &str = r#"
#[trust_vc::trait_spec]
trait Container<A> { fn combine(&self, x: A) -> A; }
struct S { v: u64 }
#[trust_vc::trait_impl]
impl Container<u64> for S {
    #[trust_vc::ensures(result == self.v + x)] fn combine(&self, x: u64) -> u64 { self.v + x }
}
#[trust_vc::requires(s.v == 3u64)]
#[trust_vc::ensures(true)]
fn cpos(s: S) { trust_vc::assert!(s.combine(4u64) == 7u64); }
#[trust_vc::requires(s.v == 3u64)]
#[trust_vc::ensures(true)]
fn cliar(s: S) { trust_vc::assert!(s.combine(4u64) == 8u64); }
"#;

// COLLISION: two DIFFERENT parameterized traits, one method name, one self-type,
// SAME return sort (no type ambiguity to confound). The keeps-first dedup would
// publish `S::get == 5` and let `s.get() == 5` verify even though the caller may
// mean `Box2` (`get == 6`) — a false-verify. The collision gate fails it closed.
const COLLISION: &str = r#"
#[trust_vc::trait_spec]
trait Container<A> { fn get(&self) -> A; }
#[trust_vc::trait_spec]
trait Box2<A> { fn get(&self) -> A; }
struct S;
#[trust_vc::trait_impl]
impl Container<u64> for S { #[trust_vc::ensures(result == 5u64)] fn get(&self) -> u64 { 5u64 } }
#[trust_vc::trait_impl]
impl Box2<u64> for S { #[trust_vc::ensures(result == 6u64)] fn get(&self) -> u64 { 6u64 } }
#[trust_vc::ensures(true)]
fn col(s: S) { trust_vc::assert!(s.get() == 5u64); }
"#;

#[test]
fn bare_type_param_return_resolves() {
    assert!(
        verified(&verify("pos", "pos", SIMPLE)),
        "a parameterized-trait method with a bare type-param return (`trait Container<A> {{ fn \
         get(&self) -> A }}`, `impl Container<u64> for S`) should resolve at a `s: S` receiver; \
         got {:?}",
        verify("pos", "pos", SIMPLE)
    );
    assert!(
        verified(&verify("fpos", "fpos", FIELD_BODY)),
        "a bare type-param return whose body reads a field should resolve; got {:?}",
        verify("fpos", "fpos", FIELD_BODY)
    );
    assert!(
        verified(&verify("cpos", "cpos", ARG_AND_RETURN)),
        "a bare type-param ARGUMENT alongside a bare type-param return \
         (`fn combine(&self, x: A) -> A`) should resolve; got {:?}",
        verify("cpos", "cpos", ARG_AND_RETURN)
    );
}

#[test]
fn bare_type_param_return_liar_fails_closed() {
    assert!(
        !verified(&verify("liar", "liar", SIMPLE)),
        "CARDINAL: a false consequence of the body axiom (`s.get() == 6`) must NOT verify"
    );
    assert!(
        !verified(&verify("fliar", "fliar", FIELD_BODY)),
        "CARDINAL: a false consequence of the field-reading body axiom must NOT verify"
    );
    assert!(
        !verified(&verify("cliar", "cliar", ARG_AND_RETURN)),
        "CARDINAL: a false consequence of the combine body axiom must NOT verify"
    );
}

#[test]
fn same_self_type_method_collision_fails_closed() {
    assert!(
        !verified(&verify("col", "col", COLLISION)),
        "CARDINAL: two parameterized-trait impls on one self-type declaring one method must fail \
         closed — the keeps-first dedup would otherwise publish a mismatched body axiom"
    );
}
