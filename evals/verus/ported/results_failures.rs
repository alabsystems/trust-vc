// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Executable counterexample cases for the active upstream Result failure
// harness, including the same custom Err shape as upstream Verus.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CustomErr {
    error_code: i32,
}

#[trust_vc::ensures(true)]
fn test_ok_result_fails() {
    trust_vc::assert!(Result::<i32, CustomErr>::Ok(1i32) is Err);
}

#[trust_vc::ensures(true)]
fn test_err_result_fails() {
    trust_vc::assert!(Result::<i32, CustomErr>::Err(CustomErr { error_code: -1i32 }) is Ok);
}
