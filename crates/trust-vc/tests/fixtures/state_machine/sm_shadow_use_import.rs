// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A bare `state_machine!` bound by a `use` from ANOTHER crate: trust-vc does
//! not own that macro, so the invocation is poisoned rather than expanded.

#![allow(dead_code, unused_variables, unused_imports)]

use trust_vc_types::int;
use verus_state_machines_macros::state_machine;

state_machine! { Imported {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn shadow_use_import_client(s: Imported::State) {}
