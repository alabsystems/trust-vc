// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Build this crate with `--cfg trust_mc`, as `targo trust-mc` builds one.

fn main() {
    println!("cargo:rustc-cfg=trust_mc");
}
