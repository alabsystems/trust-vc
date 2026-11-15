// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 PROBES, part 3: the ITEM kinds that redefine a spec-collection name
// without being a struct/enum/type-alias DECLARATION — a `use ... as <name>`
// RENAME and a `trait`. Every `_cx` body ALWAYS divides by zero.
//
// `Set` is deliberately NOT shadowed here: it is the liar twin, and it must
// keep verifying in this very file, so the rule is proved PER NAME rather than
// per file.
mod rw_inner {
    pub struct Carrier {
        pub d: Vec<u64>,
    }
}

use rw_inner::Carrier as Seq;

trait Multiset {
    fn new() -> u64;
}

#[trust_vc::ensures(true)]
fn rw1_use_alias_param_cx(v: Seq<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw2_use_alias_ctor_cx() {
    let v = Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw3_trait_named_multiset_ctor_cx() {
    let v = Multiset::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw4_trait_named_multiset_param_cx(v: Multiset<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RW5 THE DECISIVE CONTROL: the identical body at the std spelling, in the same
// file. A non-verify before and after.
#[trust_vc::ensures(true)]
fn rw5_control_plain_vec_cx(v: Vec<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RW6 THE LIAR TWIN, and the reason this rule is keyed on the NAME and not on
// the file: `Set` is redefined by nothing here, so an honest spec body over it
// must still VERIFY even though `Seq` and `Multiset` in the same file do not.
#[trust_vc::ensures(true)]
fn rw6_unshadowed_spec_set_ok(s: Set<u64>) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

// RW7 THE REFUTED HALF of RW6: the same body at the same element width behind
// an EXEC container is still CHECKED.
#[trust_vc::ensures(true)]
fn rw7_exec_set_same_body_cx(s: BTreeSet<u64>) {
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw1_use_alias_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw2_use_alias_ctor_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw3_trait_named_multiset_ctor_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rw4_trait_named_multiset_param_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
