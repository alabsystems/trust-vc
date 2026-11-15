// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A bare `state_machine!` bound by nothing: poisoned, and reported as an
//! unscannable entry at the invocation line by `cargo trust-vc check`.

#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

state_machine! { Bare {
    fields { pub t: int }

    transition! {
        tr() {
            update t = pre.t + 1;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn bare_unbound_client(s: Bare::State) {}
