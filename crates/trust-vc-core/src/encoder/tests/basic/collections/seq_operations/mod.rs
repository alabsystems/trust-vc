//! Seq operations: view (#1748), push, update, first/last, add (#2085),
//! drop_last, take, skip/drop_first, subrange, and concat.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from basic/collections.rs (#2145).

use super::*;

mod access_and_reverse;
mod count;
mod projections_and_add;
mod slices_and_concat;
mod view_and_updates;
