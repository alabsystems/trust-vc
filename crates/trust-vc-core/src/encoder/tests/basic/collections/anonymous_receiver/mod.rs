//! Typed anonymous receiver tests — contains, contains_key, and remove
//! on anonymous (non-named) Set/Seq/Map receivers with term-keyed metadata.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from basic/collections.rs (#2145).

use super::*;

mod contains;
mod overflow_and_map_values;
mod remove_and_metadata;
