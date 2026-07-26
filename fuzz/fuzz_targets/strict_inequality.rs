#![no_main]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0


use trust_vc_fuzz::{assert_not_verified, strict_inequality_program};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    assert_not_verified(strict_inequality_program(data));
});
