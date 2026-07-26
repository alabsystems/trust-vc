// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Datatype-constructor match encoding tests (#1942 Slices 3-4).

use super::*;

use crate::ir::{ArithOp, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, StructPatternField, TrustVcExpr};
use crate::vc::VariableDecl;

mod constructor_patterns;
mod setup_and_e2e;
mod struct_patterns;

fn option_u64_ty() -> TrustVcType {
    TrustVcType::from_str("Option<u64>").expect("Option<u64> should parse")
}

fn u64_ty() -> TrustVcType {
    TrustVcType::Uint { width: 64 }
}

fn option_u64_encoding(
    encoder: &mut AYEncoder,
) -> (crate::encoder::datatype::DatatypeEncoding, TrustVcType) {
    let option_ty = option_u64_ty();
    let TrustVcType::Datatype { name, variants } = &option_ty else {
        panic!("Option<u64> should be a datatype");
    };
    (
        encoder
            .register_datatype(name, variants)
            .expect("datatype registration should succeed"),
        option_ty,
    )
}

fn counter_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![crate::ir::DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), u64_ty()),
                ("max".to_string(), u64_ty()),
            ],
        )],
    }
}

fn counter_encoding(
    encoder: &mut AYEncoder,
) -> (crate::encoder::datatype::DatatypeEncoding, TrustVcType) {
    let counter_ty = counter_ty();
    let TrustVcType::Datatype { name, variants } = &counter_ty else {
        panic!("Counter should be a datatype");
    };
    (
        encoder
            .register_datatype(name, variants)
            .expect("datatype registration should succeed"),
        counter_ty,
    )
}
