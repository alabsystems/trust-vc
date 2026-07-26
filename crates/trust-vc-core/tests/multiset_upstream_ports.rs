// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Faithful 1:1 ports of the upstream Verus `rust_verify_test/tests/multiset.rs`
//! cases (`multiset_basics`, `multiset_fail`, `multiset_fail2`, `multiset_fail3`,
//! `multiset_fail4`), exercised through the TrustVc surface and verified via
//! `verify_function_from_file` (mirrors `set_map_forall_by.rs`).
//!
//! Upstream verdicts: `multiset_basics => Ok(())` (every proof fn verifies); the
//! four `*_fail` cases each have exactly one failing obligation
//! (`assert_one_fails`), which TrustVc surfaces as a `Counterexample`.
//!
//! Surface mapping (faithful, no weakening):
//!   * `a =~= b`  (extensional eq)  -> `trust_vc::assert!(trust_vc::ext_eq!(a, b))`
//!   * `a === b`  (strict/`equal`)  -> `#[trust_vc::ensures(a == b)]` (Multiset
//!     `==` lowers to Compare::Eq over the Array count carrier, which is exactly
//!     Verus strict multiset equality).
//!   * `a !== b`                     -> `a != b`
//!   * `m.choose()`, `.count`, `.add`, `.sub`, `.insert`, `.len`, `.subset_of`
//!     map to the identically-named Multiset surface methods.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/multiset_upstream_ports");
    fs::create_dir_all(dir).unwrap();
    // Key the temp file by CONTENT, not just function name: `basics_sub_add_cancel`
    // and `fail3_sub_add_cancel` both verify a fn named `sub_add_cancel`, and under
    // the default parallel test runner the two tests raced on the shared
    // `sub_add_cancel.rs` path — fail3 could read basics' TRUE variant (spurious
    // "got Ok(Verified)" alarm) or either could tear mid-write (parse error).
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

fn counterexample(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Counterexample { .. }))
}

const PRELUDE: &str = "use trust_vc_types::Multiset;\n";

fn src(body: &str) -> String {
    format!("{PRELUDE}{body}")
}

// ═══════════════════════════ multiset_basics => Ok(()) ═══════════════════════════
// Every one of the eight upstream `multiset_basics` proof fns must verify.

#[test]
fn basics_commutative() {
    let code = src(r#"
#[trust_vc::ensures(a.add(b) == b.add(a))]
fn commutative<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), b.add(a)));
}
"#);
    let r = verify(&code, "commutative");
    assert!(verified(&r), "basics::commutative must verify, got {:?}", r);
}

#[test]
fn basics_associative() {
    let code = src(r#"
#[trust_vc::ensures(a.add(b.add(c)) == a.add(b).add(c))]
fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b.add(c)), a.add(b).add(c)));
}
"#);
    let r = verify(&code, "associative");
    assert!(verified(&r), "basics::associative must verify, got {:?}", r);
}

#[test]
fn basics_insert2() {
    let code = src(r#"
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b) == Multiset::<V>::empty().insert(b).insert(a))]
fn insert2<V>(a: V, b: V) {
    trust_vc::assert!(trust_vc::ext_eq!(
        Multiset::<V>::empty().insert(a).insert(b),
        Multiset::<V>::empty().insert(b).insert(a)
    ));
}
"#);
    let r = verify(&code, "insert2");
    assert!(verified(&r), "basics::insert2 must verify, got {:?}", r);
}

#[test]
fn basics_insert2_count() {
    let code = src(r#"
#[trust_vc::requires(a != b && b != c && c != a)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(b) == 1usize)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(c) == 0usize)]
fn insert2_count<V>(a: V, b: V, c: V) {}
"#);
    let r = verify(&code, "insert2_count");
    assert!(
        verified(&r),
        "basics::insert2_count must verify, got {:?}",
        r
    );
}

#[test]
fn basics_add_sub_cancel() {
    let code = src(r#"
#[trust_vc::ensures(a.add(b).sub(b) == a)]
fn add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b).sub(b), a));
}
"#);
    let r = verify(&code, "add_sub_cancel");
    assert!(
        verified(&r),
        "basics::add_sub_cancel must verify, got {:?}",
        r
    );
}

#[test]
fn basics_sub_add_cancel() {
    let code = src(r#"
#[trust_vc::requires(b.subset_of(a))]
#[trust_vc::ensures(a.sub(b).add(b) == a)]
fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
}
"#);
    let r = verify(&code, "sub_add_cancel");
    assert!(
        verified(&r),
        "basics::sub_add_cancel must verify, got {:?}",
        r
    );
}

#[test]
fn basics_choose_count() {
    let code = src(r#"
#[trust_vc::requires(m.len() != 0usize)]
#[trust_vc::ensures(true)]
fn choose_count<V>(m: Multiset<V>) {
    trust_vc::assert!(m.count(m.choose()) > 0usize);
}
"#);
    let r = verify(&code, "choose_count");
    assert!(
        verified(&r),
        "basics::choose_count must verify, got {:?}",
        r
    );
}

#[test]
fn basics_len_is_zero_if_count_for_each_value_is_zero() {
    // FEATURE B: choose-positivity must fire under the `if m.len() != 0` branch
    // guard (not only when len != 0 is a top-level requires).
    let code = src(r#"
#[trust_vc::requires(forall(|v: V| m.count(v) == 0u64))]
#[trust_vc::ensures(m.len() == 0usize)]
fn len_is_zero_if_count_for_each_value_is_zero<V>(m: Multiset<V>) {
    if m.len() != 0usize {
        trust_vc::assert!(m.count(m.choose()) > 0usize);
    }
}
"#);
    let r = verify(&code, "len_is_zero_if_count_for_each_value_is_zero");
    assert!(verified(&r), "basics::len_zero must verify, got {:?}", r);
}

// ═══════════════════════════ multiset_fail => Err (one failure) ═══════════════════
#[test]
fn fail_insert2_fail() {
    // Missing precondition `a != b`: count(a) need not be 1.
    let code = src(r#"
#[trust_vc::ensures(true)]
fn insert2_fail<V>(a: V, b: V, c: V) {
    trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize);
}
"#);
    let r = verify(&code, "insert2_fail");
    assert!(
        counterexample(&r),
        "fail::insert2_fail must be Counterexample, got {:?}",
        r
    );
}

// ═══════════════════════════ multiset_fail2 => Err (FEATURE A) ════════════════════
#[test]
fn fail2_add_fail() {
    // `a.add(b) =~= a.add(a)` is genuinely false (witness: any v with
    // count(a,v) != count(b,v)).
    let code = src(r#"
#[trust_vc::ensures(a.add(b) == a.add(a))]
fn add_fail<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), a.add(a)));
}
"#);
    let r = verify(&code, "add_fail");
    assert!(
        counterexample(&r),
        "fail2::add_fail must be Counterexample, got {:?}",
        r
    );
}

// ═══════════════════════════ multiset_fail3 => Err (FEATURE A) ════════════════════
#[test]
fn fail3_sub_add_cancel() {
    // Missing `b.subset_of(a)`: `a.sub(b).add(b) =~= a` is false where b has
    // more of some element than a.
    let code = src(r#"
#[trust_vc::ensures(a.sub(b).add(b) == a)]
fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
}
"#);
    let r = verify(&code, "sub_add_cancel");
    assert!(
        counterexample(&r),
        "fail3::sub_add_cancel must be Counterexample, got {:?}",
        r
    );
}

// ═══════════════════════════ multiset_fail4 => Err ════════════════════════════════
#[test]
fn fail4_choose_count() {
    // Missing precondition `m.len() != 0`.
    let code = src(r#"
#[trust_vc::ensures(true)]
fn choose_count_fail<V>(m: Multiset<V>) {
    trust_vc::assert!(m.count(m.choose()) > 0usize);
}
"#);
    let r = verify(&code, "choose_count_fail");
    assert!(
        counterexample(&r),
        "fail4::choose_count must be Counterexample, got {:?}",
        r
    );
}

// ═══════════════════════ ADVERSARIAL SOUNDNESS GUARDS ═══════════════════════
// Feature A must NOT turn a TRUE `=~=` into a false counterexample, and Feature B
// must NOT spuriously preserve choose-positivity for a modified/empty multiset or
// under a guard that does not establish non-emptiness.

/// Feature A soundness: a genuinely TRUE multiset `=~=` (commutativity of add)
/// must VERIFY — the compositional witness path must never fabricate a
/// differing-count counterexample for an equality that holds pointwise.
#[test]
fn adversarial_true_add_commute_ext_eq_verifies() {
    let code = src(r#"
#[trust_vc::ensures(true)]
fn adv_true_add_commute<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), b.add(a)));
}
"#);
    let r = verify(&code, "adv_true_add_commute");
    assert!(
        verified(&r),
        "TRUE a.add(b) =~= b.add(a) must verify, got {:?}",
        r
    );
}

/// Feature A soundness: a TRUE `==` (strict) over multisets must VERIFY via the
/// same Skolem-witness refutation routing.
#[test]
fn adversarial_true_add_sub_cancel_direct_eq_verifies() {
    let code = src(r#"
#[trust_vc::ensures(a.add(b).sub(b) == a)]
fn adv_true_add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>) {}
"#);
    let r = verify(&code, "adv_true_add_sub_cancel");
    assert!(
        verified(&r),
        "TRUE a.add(b).sub(b) == a must verify, got {:?}",
        r
    );
}

/// Feature A soundness: a FALSE `=~=` body assert (no ensures) must produce a
/// concrete Counterexample, not Unknown.
#[test]
fn adversarial_false_add_ext_eq_counterexample() {
    let code = src(r#"
#[trust_vc::ensures(true)]
fn adv_false_add_ext_eq<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), a.add(a)));
}
"#);
    let r = verify(&code, "adv_false_add_ext_eq");
    assert!(
        counterexample(&r),
        "FALSE a.add(b) =~= a.add(a) must be Counterexample, got {:?}",
        r
    );
}

/// Feature B soundness: the WRONG guard `m.len() == 0` (which establishes that
/// `m` is EMPTY) must NOT let `m.count(m.choose()) > 0` verify — choose-positivity
/// is vacuous for an empty multiset, so this must fail closed.
#[test]
fn adversarial_choose_under_empty_guard_does_not_verify() {
    let code = src(r#"
#[trust_vc::ensures(true)]
fn adv_choose_empty_guard<V>(m: Multiset<V>) {
    if m.len() == 0usize {
        trust_vc::assert!(m.count(m.choose()) > 0usize);
    }
}
"#);
    let r = verify(&code, "adv_choose_empty_guard");
    assert!(
        !verified(&r),
        "choose-positivity under len==0 guard must NOT verify, got {:?}",
        r
    );
}

/// Feature B soundness: a branch guard on a DIFFERENT multiset (`a`) must NOT
/// transfer choose-positivity to `b` — `b` may be empty even when `a` is not.
#[test]
fn adversarial_choose_cross_multiset_guard_does_not_verify() {
    let code = src(r#"
#[trust_vc::ensures(true)]
fn adv_choose_cross<V>(a: Multiset<V>, b: Multiset<V>) {
    if a.len() != 0usize {
        trust_vc::assert!(b.count(b.choose()) > 0usize);
    }
}
"#);
    let r = verify(&code, "adv_choose_cross");
    assert!(
        !verified(&r),
        "cross-multiset guard must NOT transfer choose-positivity, got {:?}",
        r
    );
}

/// Feature B soundness: with NO guard at all, choose-positivity must fail closed
/// (the multiset may be empty). Complements `fail4_choose_count`.
#[test]
fn adversarial_choose_no_guard_does_not_verify() {
    let code = src(r#"
#[trust_vc::ensures(true)]
fn adv_choose_no_guard<V>(m: Multiset<V>) {
    trust_vc::assert!(m.count(m.choose()) > 0usize);
}
"#);
    let r = verify(&code, "adv_choose_no_guard");
    assert!(
        !verified(&r),
        "unguarded choose-positivity must NOT verify, got {:?}",
        r
    );
}
