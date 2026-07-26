//! Basic encoder tests — split by domain for maintainability.
//!
//! Originally a single 1535-line monolith (`basic.rs`), now split into
//! domain-focused modules to reduce ownership conflicts and improve
//! test discoverability. Part of #1962.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod collections;
mod parser_and_operators;
mod soundness;
mod type_sorts;
mod verification_pipeline;
