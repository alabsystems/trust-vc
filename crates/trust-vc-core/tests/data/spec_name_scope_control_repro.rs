// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 LIAR TWIN: the GENUINE spec surface, in a file that redefines
// nothing. Every one of these must keep VERIFYING — the round-10 scope rule
// may not be satisfied by refusing the ghost surface outright.
struct RvGhostHolder {
    data: Seq<u64>,
}

#[trust_vc::ensures(true)]
fn rv1_genuine_spec_param_ok(v: Seq<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv2_genuine_spec_field_ok(b: RvGhostHolder) {
    let _ = b.data.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv3_genuine_spec_local_let_ok() {
    let s: Seq<u64> = Seq::empty();
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv4_genuine_ctor_local_ok() {
    let s = Seq::empty();
    let _ = s.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv5_genuine_ctor_sink_ok(n: u64) {
    let _ = Seq::new(n, |i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv6_genuine_specfn_sink_ok() {
    let _ = SpecFn::new(|x| x + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv7_genuine_spec_tuple_component_ok(t: (Seq<u64>, u64)) {
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}

// THE REFUTED HALVES: the same bodies at the same element width behind an EXEC
// container must still be CHECKED, so the pins above cannot be satisfied by
// "collection receivers are always skipped".
#[trust_vc::ensures(true)]
fn rv1b_exec_param_cx(v: Vec<u64>) {
    let _ = v.map(|i| i + 1);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn rv7b_exec_tuple_component_cx(t: (Vec<u64>, u64)) {
    let _ = t.0.map(|i| i + 1);
    trust_vc::assert!(true);
}
