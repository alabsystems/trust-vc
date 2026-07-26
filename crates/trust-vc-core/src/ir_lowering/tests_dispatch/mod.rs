// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for dispatch-family expression lowering (methods, calls, collections,
//! constructors, casts, quantifiers, SpecFn, and higher-order combinators).

mod support;

mod calls;
mod casts_index;
mod collections;
mod constructors;
mod ghost;
mod higher_order;
mod macros;
mod metadata;
mod methods;
mod prophecy;
mod spec_fn;
