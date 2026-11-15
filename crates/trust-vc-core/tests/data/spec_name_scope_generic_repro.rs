// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 PROBES: a user type that shares a spec collection's NAME and IS
// written WITH arguments — the residual round 9 disclosed as still open.
// Every `_cx` body ALWAYS divides by zero.
type Seq<T> = Vec<T>;

mod r_inner {
    pub type Set<T> = BTreeSet<T>;
}
use r_inner::Set;

struct Map<'a> {
    d: &'a u64,
}

struct Multiset<const N: usize> {
    d: u64,
}

struct RS5Holder {
    data: Seq<u64>,
}

#[trust_vc::ensures(true)]
fn rs1_generic_alias_seq_cx(v: Seq<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs1b_control_plain_vec_cx(v: Vec<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs2_reexport_generic_set_cx(v: Set<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs2b_control_plain_btreeset_cx(v: BTreeSet<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs3_lifetime_only_map_cx<'a>(m: Map<'a>) {
    let _ = m.map_values(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs4_const_generic_multiset_cx(v: Multiset<3>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs5_field_spelled_with_generic_alias_cx(b: RS5Holder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs6_generic_alias_local_let_cx() {
    let v: Seq<u64> = Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs1_generic_alias_seq_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs2_reexport_generic_set_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs3_lifetime_only_map_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs4_const_generic_multiset_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs5_field_spelled_with_generic_alias_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rs6_generic_alias_local_let_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
