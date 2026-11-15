// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// ROUND-10 PROBES, part 2: the OTHER bare-name consumers of the four
// spec-collection names — the ghost-collection CONSTRUCTOR-AS-SINK route
// (`Seq::new(n, |i| ..)`), the `SpecFn`/`FnSpec` sink, and a user STRUCT
// (not an alias) carrying the name.
struct Seq {
    d: Vec<u64>,
}

impl Seq {
    fn new() -> Seq {
        Seq { d: Vec::new() }
    }

    fn build(_n: u64, _f: impl Fn(u64) -> u64) -> Seq {
        Seq { d: Vec::new() }
    }
}

type SpecFn = u64;
type RuPlain = u64;

#[trust_vc::ensures(true)]
fn ru1_user_struct_named_seq_ctor_cx() {
    let v = Seq::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru2_ctor_as_sink_cx() {
    let _ = Seq::build(3u64, |_i| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru2b_ctor_as_sink_control_cx() {
    let _ = RuPlain::build(3u64, |_i| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru3_specfn_sink_cx() {
    let _ = SpecFn::new(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru3b_specfn_sink_control_cx() {
    let _ = RuPlain::new(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru4_ctor_chain_cx() {
    let v = Seq::new().push(1u64);
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru5_ctor_turbofish_cx() {
    let v = Seq::<u64>::new();
    let _ = v.map(|_x| 10u64 / 0u64);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru1_user_struct_named_seq_ctor_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru2_ctor_as_sink_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru3_specfn_sink_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru4_ctor_chain_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn ru5_ctor_turbofish_nosink() {
    let _g = |_x: u64| 10u64 / 0u64;
    trust_vc::assert!(true);
}
