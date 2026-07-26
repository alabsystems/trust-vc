// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bitwise operation and overflow check verification tests — split into
//! domain submodules.
//!
//! Original monolith (914 lines) split for maintainability (#2145).

use super::*;

mod bitwise;
mod overflow_checks;
mod signed_overflow_shift;
