// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that all_triggers can only be applied to functions.

use trust_vc::all_triggers;

#[all_triggers]
const CONSTANT: i32 = 42;

fn main() {}