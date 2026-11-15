// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `mod trust_vc { .. }` rebinds the root, so `trust_vc::state_machine!` is
//! NOT trust-vc's macro here.

#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

mod trust_vc {}

trust_vc::state_machine! { Rebound {
    fields { pub t: int }
} }

#[::trust_vc::proof]
#[::trust_vc::ensures(true)]
fn shadow_rebound_root_client(s: Rebound::State) {}
