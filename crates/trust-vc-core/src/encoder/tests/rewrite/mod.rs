//! Tests for pre-state variable substitution (string and typed paths).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{i32_ty, int_lit, make_vars, var};
use crate::encoder::verification::rewrite::{
    collect_pre_state_target_names, replace_vars_with_pre, replace_vars_with_pre_typed,
    replace_vars_with_pre_typed_with_targets, replace_whole_word,
};
use crate::ir::{ArithOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr, TrustVcType};
use crate::vc::VariableDecl;
mod place_roots;
mod string_rewrite;
mod typed_basics;
mod typed_shadowing;
