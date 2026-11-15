//! Expression dispatch lowering by call family.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

mod calls;
mod casts;
#[path = "../dispatch_collections.rs"]
mod collections;
mod macros;
mod methods;
mod option_closure;
mod spec_closure;

pub(super) use calls::lower_call;
pub(super) use casts::{lower_cast, lower_index};
pub(super) use macros::lower_macro_expr;
pub(super) use methods::{lower_field_access, lower_method_call, lower_struct_literal};
// Re-exported crate-wide for the inline-body type monomorphizer
// (encoder::eval::substitution_inline): pure `TypeParam`→concrete substitution
// with structural recursion and tuple-carrier renormalization, and NO arbitrary
// datatype-carrier renaming (unlike `TrustVcType::monomorphize`).
pub(crate) use methods::substitute_type_params;
// The extractor-synthesized unwrap-family precondition markers (H3): emitted by
// `vc_extraction::body_extract`, lowered only on `Option` / `Result` receivers.
pub(crate) use methods::{UNWRAP_ERR_REQUIRES_MARKER, UNWRAP_REQUIRES_MARKER};

// The one collection-result typing rule, re-read by the IR typing validator.
pub(super) use collections::infer_collection_op_type;
