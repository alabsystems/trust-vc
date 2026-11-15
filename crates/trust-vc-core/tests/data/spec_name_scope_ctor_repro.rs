// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 PROBES: the ghost-collection CONSTRUCTOR path and the ghost
// COLLECTION MACRO, both of which key on the bare NAME and neither of which
// round 9's argument-list narrowing reaches. Every `_cx` body ALWAYS divides
// by zero.
type Seq = Vec<u64>;
type Set = BTreeSet<u64>;
type RtPlainVec = Vec<u64>;

macro_rules! seq {
    ($($x:expr),*) => {
        Vec::new()
    };
}

macro_rules! rtvec {
    ($($x:expr),*) => {
        Vec::new()
    };
}

#[trust_vc::ensures(true)]
fn rt1_ctor_alias_named_seq_cx() {
    let v = Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// RT1B THE DECISIVE CONTROL: the identical body whose alias is NOT named after
// a spec collection. Only the NAME may distinguish them.
#[trust_vc::ensures(true)]
fn rt1b_ctor_control_plain_alias_cx() {
    let v = RtPlainVec::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt1c_ctor_control_std_vec_cx() {
    let v = Vec::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt2_ctor_alias_named_set_cx() {
    let v = Set::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt2b_ctor_control_btreeset_cx() {
    let v = BTreeSet::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt3_ctor_annotated_alias_cx() {
    let v: Seq = Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt4_macro_named_seq_cx() {
    let _ = seq![1u64, 2u64].map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt4b_macro_control_named_rtvec_cx() {
    let _ = rtvec![1u64, 2u64].map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt5_macro_bound_local_cx() {
    let v = seq![1u64, 2u64];
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt6_ctor_module_qualified_cx() {
    let v = std::collections::Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt1_ctor_alias_named_seq_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt2_ctor_alias_named_set_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt3_ctor_annotated_alias_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt4_macro_named_seq_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt5_macro_bound_local_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rt6_ctor_module_qualified_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
