// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-9 LIAR TWIN for `spec_collection_name_shadow_repro.rs`. Identical
// receivers written at the GENUINE spec spellings, with no shadowing alias in
// the file. These are honest spec bodies and must keep VERIFYING: the round-9
// narrowing may not be satisfied by refusing the spec surface.
struct ZvGhostFieldHolder {
    data: Seq<u64>,
}

#[trust_vc::ensures(true)]
fn zv6_genuine_spec_seq_ok(v: Seq<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv7_genuine_spec_set_ok(v: Set<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv8_genuine_spec_map_ok(m: Map<u64, u64>) {
    let _ = m.map_values(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn zv9_genuine_spec_seq_field_ok(b: ZvGhostFieldHolder) {
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

// ZV10 THE REFUTED HALF of the decisive pair, so the four `Verified` pins above
// cannot be satisfied by "spec receivers are always skipped": the same body at
// the same element width behind an EXEC container must still be CHECKED.
#[trust_vc::ensures(true)]
fn zv10_exec_vec_same_body_cx(v: Vec<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}
