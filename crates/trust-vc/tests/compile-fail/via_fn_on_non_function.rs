// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that via_fn can only be applied to functions.

use trust_vc::via_fn;

#[via_fn]
impl SomeType {
    fn method(&self) {}
}

fn main() {}