// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-9 FIXTURES: a user TYPE ALIAS that merely SHARES the NAME of a spec
// collection. Every closure body below ALWAYS divides by zero, so a `Verified`
// is a FALSE VERIFY. These aliases shadow the spec names for the WHOLE file,
// which is why the honest spec twins live in the companion
// `spec_collection_name_shadow_control_repro.rs` instead.
type Seq = Vec<u64>;
type Set = BTreeSet<u64>;
type Map = BTreeMap<u64, u64>;

struct ZvAliasFieldHolder {
    data: Seq,
}

#[trust_vc::ensures(true)]
fn zv1_alias_named_seq_over_vec_cx(v: Seq) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZV1B THE DECISIVE CONTROL: the identical body at the std spelling the alias
// names. A non-verify before and after, so only the NAME distinguishes them.
#[trust_vc::ensures(true)]
fn zv1b_control_plain_vec_cx(v: Vec<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv2_alias_named_set_over_btreeset_cx(v: Set) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv2b_control_plain_btreeset_cx(v: BTreeSet<u64>) {
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv3_alias_named_map_over_btreemap_cx(m: Map) {
    let _ = m.map_values(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv3b_control_plain_btreemap_cx(m: BTreeMap<u64, u64>) {
    let _ = m.map_values(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZV4 the same shadowing reached through a struct FIELD, i.e. round 7's
// field-provenance seam reading the same table.
#[trust_vc::ensures(true)]
fn zv4_field_spelled_with_the_alias_cx(b: ZvAliasFieldHolder) {
    let _ = b.data.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

// ZV5 the no-sink twin: the same always-panicking closure handed to nothing.
#[trust_vc::ensures(true)]
fn zv5_no_sink_twin(v: Vec<u64>) {
    let _g = |_x| 10u64 / 0u64;
    trust_vc::assert!(true);
}
