// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch-specific test fixtures (datatype helpers).

use crate::ir::{DatatypeVariant, TrustVcType};

pub(super) fn counter_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), TrustVcType::Uint { width: 32 }),
                ("max".to_string(), TrustVcType::Uint { width: 32 }),
            ],
        )],
    }
}

pub(super) fn outer_counter_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "OuterCounter".to_string(),
        variants: vec![DatatypeVariant::new(
            "OuterCounter",
            vec![
                ("inner".to_string(), counter_ty()),
                ("flag".to_string(), TrustVcType::Bool),
            ],
        )],
    }
}

pub(super) fn option_u64_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Option<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new("None", vec![]),
            DatatypeVariant::new(
                "Some",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
        ],
    }
}

pub(super) fn generic_choice_template_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Choice".to_string(),
        variants: vec![
            DatatypeVariant::new(
                "First",
                vec![("0".to_string(), TrustVcType::TypeParam("A".to_string()))],
            ),
            DatatypeVariant::new("Empty", vec![]),
        ],
    }
}
