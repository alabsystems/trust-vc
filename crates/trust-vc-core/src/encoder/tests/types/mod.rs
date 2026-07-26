// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for encoder/types.rs — BV range, type helpers, width inference.

mod sort_mapping;
mod verification;
mod width;

use super::result_oracles::{expect_counterexample, expect_not_verified, expect_verified};
use crate::encoder::types::{
    fits_in_bv, fits_in_signed_bv, infer_int_width_from_types, min_bv_width_for_value,
    min_signed_bv_width_for_value, quantifier_sort_for_type, sort_for_type,
};
#[allow(unused_imports)]
use crate::ir::{pointer_width, TrustVcType};
use crate::type_syntax::split_generic_args;
use crate::vc::ProofObligation;
use ay_dpll::api::Sort;
