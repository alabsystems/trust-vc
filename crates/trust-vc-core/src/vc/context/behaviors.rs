//! Arithmetic and verification behavior policies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `context.rs` for the 500-line limit (#2621).

/// Controls whether obligations are checked from the function body or call site perspective.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum VerificationMode {
    /// Verify the function body: requires are assumed, ensures are asserted.
    #[default]
    BodyLevel,
    /// Verify a call site: requires are asserted, ensures are assumed.
    CallSite,
}

/// Policy for arithmetic overflow checking, modeled after Verus's
/// `OverflowBehavior` (`verus/source/vir/src/ast.rs:557-597`).
///
/// In Verus, the behavior is mode-dependent:
/// - **Exec** → `Error`: assert no overflow, then assume for downstream
/// - **Proof/Spec** → `Allow`: pure mathematical integers, no checking
///
/// `Truncate` applies range-clipping without asserting, useful for
/// ghost code that needs modular semantics but shouldn't fail on overflow.
///
/// Part of #2516.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum OverflowBehavior {
    /// Assert overflow predicate, then assume it for downstream reasoning.
    /// Verification fails if overflow is possible. Used for exec mode.
    Error,
    /// Apply range-clipping (uClip/iClip) but do not assert. Ghost code
    /// can overflow freely but gets modular semantics.
    Truncate,
    /// No clipping, no assertion. Pure mathematical integers.
    /// Default — matches the old `check_overflow: false` behavior.
    #[default]
    Allow,
}

impl OverflowBehavior {
    /// Derive the overflow behavior from a function's mode.
    ///
    /// Exec → Error (assert+assume), Proof/Spec → Allow (math integers).
    #[must_use]
    pub fn from_mode(mode: crate::mode::FunctionMode) -> Self {
        match mode {
            crate::mode::FunctionMode::Exec => Self::Error,
            crate::mode::FunctionMode::Proof | crate::mode::FunctionMode::Spec => Self::Allow,
        }
    }

    /// Whether overflow checking assertions should be generated.
    /// True for `Error` only — `Truncate` clips without asserting.
    #[must_use]
    pub const fn should_check(&self) -> bool {
        matches!(self, Self::Error)
    }

    /// Whether the result should be clipped to the type's range.
    /// True for `Error` and `Truncate` — `Allow` uses unbounded integers.
    #[must_use]
    pub const fn should_clip(&self) -> bool {
        matches!(self, Self::Error | Self::Truncate)
    }

    /// The default behavior when overflow checking is disabled.
    /// Used for backward compatibility with `check_overflow: false`.
    #[must_use]
    pub const fn default_no_check() -> Self {
        Self::Allow
    }
}

/// Policy for division-by-zero checking.
///
/// Modeled after Verus's `Div0Behavior`. In exec mode, division by zero
/// is an error; in spec mode, it may be allowed (returning an unspecified
/// value) to simplify specifications.
///
/// Part of #2516.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum Div0Behavior {
    /// Assert divisor is non-zero. Used for exec mode.
    Error,
    /// Allow division by zero (unspecified result). Default — matches
    /// `OverflowBehavior::Allow` for consistent no-check baseline.
    #[default]
    Allow,
}

impl Div0Behavior {
    /// Derive from function mode: exec → Error, proof/spec → Allow.
    #[must_use]
    pub fn from_mode(mode: crate::mode::FunctionMode) -> Self {
        match mode {
            crate::mode::FunctionMode::Exec => Self::Error,
            crate::mode::FunctionMode::Proof | crate::mode::FunctionMode::Spec => Self::Allow,
        }
    }

    /// Returns whether division-by-zero assertions should be generated.
    #[must_use]
    pub fn should_check(&self) -> bool {
        matches!(self, Self::Error)
    }
}

/// Policy for shift amount bounds checking.
///
/// Modeled after Verus's `BitshiftBehavior`. Shift amounts exceeding the
/// bit width produce undefined behavior in Rust; in exec mode this is an
/// error, in spec mode it may be allowed.
///
/// Part of #2516.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum BitshiftBehavior {
    /// Assert shift amount < bit width. Default — shift UB is always
    /// checked in BV mode regardless of overflow mode. In int-mode
    /// (spec/proof), shift UB doesn't exist.
    #[default]
    Error,
    /// Allow over-shifts (unspecified result). Must be set explicitly.
    Allow,
}

impl BitshiftBehavior {
    /// Derive from function mode: exec → Error, proof/spec → Allow.
    #[must_use]
    pub fn from_mode(mode: crate::mode::FunctionMode) -> Self {
        match mode {
            crate::mode::FunctionMode::Exec => Self::Error,
            crate::mode::FunctionMode::Proof | crate::mode::FunctionMode::Spec => Self::Allow,
        }
    }

    /// Returns whether shift-bounds assertions should be generated.
    #[must_use]
    pub fn should_check(&self) -> bool {
        matches!(self, Self::Error)
    }
}
