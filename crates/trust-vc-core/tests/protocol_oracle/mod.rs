// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Random raw protocol obligations and their verdicts, computed without ty:
//! the oracle `protocol_lane_oracle` holds the ty lane to.

pub mod case;
pub mod expr;
pub mod gen;
pub mod model;
