// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[trust_vc::ensures(true)]
unsafe fn unsafe_fns_ok() {}

#[trust_vc::proof]
unsafe fn unsafe_proof_fn_fail() {}
