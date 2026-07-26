// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[path = "substitution_inline.rs"]
mod inline;
#[path = "substitution_vars.rs"]
mod vars;

pub(in crate::encoder) use inline::substitute_inline_calls;
pub(in crate::encoder) use vars::substitute_vars_in_expr;
