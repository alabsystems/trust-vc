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
