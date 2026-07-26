// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

use trust_vc_types::Seq;

#[trust_vc::contract(ensures(true), returns(result))]
fn contradiction_test() {
    trust_vc::assert_by_contradiction!(1u64 == 0u64 + 1u64, {
        trust_vc::assert!(false);
    });
}

#[trust_vc::contract(ensures(true), returns(result))]
fn map_test() {
    trust_vc::assert!(trust_vc::ext_eq!(
        trust_vc_types::map![1u64 => true, 2u64 => false],
        trust_vc_types::map![1u64 => true, 2u64 => false]
    ));
}

#[trust_vc::contract(ensures(true), returns(result))]
fn seq_test() {
    trust_vc::assert!(trust_vc::ext_eq!(
        trust_vc_types::seq![true, false],
        Seq::<bool>::empty().push(true).push(false)
    ));
}

#[trust_vc::contract(requires(x + y == z), ensures(true), returns(result))]
fn calc_test(x: u64, y: u64, z: u64) {
    trust_vc::calc! {
        (==)
        x + y;
        (==) {} z;
    };
}

#[trust_vc::contract(requires(x + y == z), ensures(true), returns(w))]
pub fn do_something(x: u64, y: u64, z: u64) -> u64 {
    calc_test(x, y, z);
    if x < y {
        x
    } else {
        z
    }
}
