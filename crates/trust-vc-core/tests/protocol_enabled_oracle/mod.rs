// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Modules over a finite universe that exercise ty's ENABLED search, and
//! their meaning, brute-forced without ty: the oracle
//! `protocol_lane_enabled_oracle` holds the ty lane to.
//!
//! The generator, the model, the reviewed shapes (both review rounds) and
//! the shape classes are ty's own semantic oracle for ENABLED
//! (`crates/tla-check/tests/enabled_semantic_oracle/` in ty main), carried
//! here unchanged so the lane is judged by the same meaning ty is judged by: `ENABLED A` holds in `s` iff some successor `t` makes `A`
//! true for `<<s, t>>`; definitions and operator arguments are expanded
//! where they are referenced; bound variables are values.

// Carried unchanged from ty, so a helper this driver does not call is still
// here, and ty's names (`E::UnchangedE`) are kept.
#![allow(dead_code, clippy::enum_variant_names)]

pub mod ast;
pub mod cases;
pub mod gen;
pub mod model;
pub mod print;
pub mod shapes;
