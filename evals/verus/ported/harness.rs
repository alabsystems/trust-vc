// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::ensures(true)]
fn harness_zero() {}

#[trust_vc::ensures(true)]
fn harness_true() {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn harness_false() {
    trust_vc::assert!(false); // FAILS
}

#[trust_vc::ensures(true)]
fn harness_macro_true() {
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn harness_macro_false() {
    trust_vc::assert!(false); // FAILS
}
