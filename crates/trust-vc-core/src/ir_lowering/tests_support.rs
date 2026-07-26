// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for the `ir_lowering` test suite.

use super::TypeEnv;
use crate::ir::TrustVcType;

pub(super) fn env_with(vars: &[(&str, &str)]) -> TypeEnv {
    let mut env = TypeEnv::new();
    for (name, ty) in vars {
        env.insert(name.to_string(), TrustVcType::from_str(ty).unwrap());
    }
    env
}
