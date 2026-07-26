//! Expression encoding tests — split into domain submodules.
//!
//! Original monolith (1,124 lines, 35 tests) split for maintainability (#2145).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod datatype_match_result_distribution;
mod division_and_width;
mod ite_block_cast;
mod match_and_misc;
mod option_methods;
mod paths_and_indexing;
mod result_methods;
