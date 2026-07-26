// Proph local integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Part of #2538: proof-local Proph<T> bindings must survive proc-macro
// expansion without invalid primitive casts.

mod common;

use trust_vc_types::Proph;

#[trust_vc::proof]
fn proof_prophecy_round_trip() {
    let p: Proph<u64> = Proph::<u64>::new();
    let v: u64 = p.view();
    p.resolve(v);
    trust_vc::assert!(v == p.view());
}

#[trust_vc::proof]
fn proof_prophecy_round_trip_qualified() {
    let p: trust_vc_types::Proph<u64> = trust_vc_types::Proph::<u64>::new();
    let v: u64 = p.view();
    p.resolve(v);
    trust_vc::assert!(v == p.view());
}

#[test]
fn proph_local_round_trip_verifies() {
    let _ = common::verify_should_pass(proof_prophecy_round_trip);
}

#[test]
fn proph_local_round_trip_qualified_verifies() {
    let _ = common::verify_should_pass(proof_prophecy_round_trip_qualified);
}
