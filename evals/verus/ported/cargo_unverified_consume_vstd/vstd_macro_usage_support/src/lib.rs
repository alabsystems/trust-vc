// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

pub fn do_something(x: u64, y: u64, z: u64) -> u64 {
    if x < y {
        x
    } else {
        z
    }
}
