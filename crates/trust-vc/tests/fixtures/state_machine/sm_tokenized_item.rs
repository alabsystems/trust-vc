// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `tokenized_state_machine!` at item position stays refused in D1a.

#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

trust_vc::tokenized_state_machine! { Tok {
    fields {
        #[sharding(variable)]
        pub t: int,
    }

    init! {
        initialize() {
            init t = 5;
        }
    }
} }

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn tokenized_item_client(s: Tok::State) {}
