// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Ghost;

#[trust_vc::ensures({
    let x: Option<usize> = Option::<usize>::None;
    x.is_none()
})]
#[trust_vc::ensures({
    let x = t.view().unwrap();
    x == x
})]
fn test_regression_78<T>(t: Ghost<Option<T>>) {}
