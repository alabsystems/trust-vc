// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

#[macro_export]
macro_rules! state_machine {
    ($($tokens:tt)*) => {
        compile_error!(
            "TrustVc does not yet implement Verus state_machine! expansion or generated proof APIs"
        );
    };
}

#[macro_export]
macro_rules! tokenized_state_machine {
    ($($tokens:tt)*) => {
        compile_error!(
            "TrustVc does not yet implement Verus tokenized_state_machine! expansion, tokens, or sharding APIs"
        );
    };
}

pub fn trust_vc_port_dependency_marker() {}
