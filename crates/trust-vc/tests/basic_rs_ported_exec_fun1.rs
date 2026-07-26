// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused executable coverage for the `test_exec_fun1` behavior added to the
//! partial upstream basic.rs TrustVc port.

mod common;

fn basic_rs_test_exec_fun1_f(_x: u64) -> u64 {
    5u64
}

fn basic_rs_test_exec_fun1_g(x: u64) -> u64 {
    basic_rs_test_exec_fun1_f(x)
}

fn basic_rs_test_exec_fun1(x: u64) {
    trust_vc::track_let! {
        let y = basic_rs_test_exec_fun1_g(x);
        trust_vc::assert!(y == 5u64);
    }
}

#[test]
fn basic_rs_test_exec_fun1_verifies() {
    let _ = common::verify_should_pass(|| {
        basic_rs_test_exec_fun1(11u64);
    });
}
