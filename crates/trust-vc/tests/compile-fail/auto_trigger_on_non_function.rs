// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that auto_trigger can only be applied to functions.

use trust_vc::auto_trigger;

#[auto_trigger]
struct NotAFunction {
    field: i32,
}

fn main() {}