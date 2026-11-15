// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A file-local `macro_rules! state_machine` keeps HEAD behaviour: the
//! invocation is left exactly as written, at the root and inside a module.

#![allow(dead_code, unused_variables, unused_macros)]

macro_rules! state_machine {
    ($($tokens:tt)*) => {};
}

state_machine! { RootLocal {
    fields { pub t: u64 }
} }

mod inner {
    macro_rules! state_machine {
        ($($tokens:tt)*) => {};
    }

    state_machine! { ModLocal {
        fields { pub t: u64 }
    } }
}

#[trust_vc::ensures(result == 3u64)]
fn shadow_local_macro_rules_client() -> u64 {
    3u64
}
