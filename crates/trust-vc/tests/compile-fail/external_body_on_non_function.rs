// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that external_body can only be applied to functions.

use trust_vc::external_body;

#[external_body]
enum NotAFunction {
    Variant1,
    Variant2,
}

fn main() {}