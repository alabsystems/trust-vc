// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Temporarily set a bool field, then restore its prior value on normal return
/// or during panic unwinding.
///
/// Two forms:
/// - `with_flag_unwind_safe!(field, new_value, { body })` — set then restore.
/// - `with_flag_unwind_safe!(field, { body })` — save and restore only
///   (the body may modify the field; the prior value is always restored).
///
/// Callers should pass a plain field path (`self.state.some_flag`) so the field
/// is read and written consistently around the protected body.
macro_rules! with_flag_unwind_safe {
    ($field:expr, $body:block) => {{
        let prior = $field;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| $body));
        $field = prior;
        match result {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }};
    ($field:expr, $value:expr, $body:block) => {{
        let prior = $field;
        $field = $value;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| $body));
        $field = prior;
        match result {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }};
}

pub(crate) use with_flag_unwind_safe;
