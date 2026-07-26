// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::ir::{TrustVcExpr, TrustVcType};

pub(super) fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Int { width: 32 },
    }
}

pub(super) fn i32_lit(v: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: v,
        ty: TrustVcType::Int { width: 32 },
    }
}
