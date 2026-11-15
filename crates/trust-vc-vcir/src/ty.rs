//! VcIR types.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ids::AdtId;

/// The integer types, following Verus: the two mathematical types and Rust's
/// machine integers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntRange {
    /// Mathematical integers (Verus `int`).
    Int,
    /// Natural numbers (Verus `nat`).
    Nat,
    /// Unsigned machine integer of the given width in bits (8 to 128).
    U(u32),
    /// Signed machine integer of the given width in bits (8 to 128).
    I(u32),
    /// `usize`; its widths are [`crate::VcCrate::architecture`].
    USize,
    /// `isize`; its widths are [`crate::VcCrate::architecture`].
    ISize,
    /// `char`, as its Unicode scalar value.
    Char,
}

/// Widths a fixed-width integer type may have.
pub const MACHINE_WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

impl IntRange {
    /// True for the machine types (everything but `Int` and `Nat`).
    #[must_use]
    pub const fn is_bounded(self) -> bool {
        !matches!(self, Self::Int | Self::Nat)
    }

    /// True for the mathematical types `Int` and `Nat`.
    #[must_use]
    pub const fn is_math(self) -> bool {
        matches!(self, Self::Int | Self::Nat)
    }

    /// True for the signed machine types.
    #[must_use]
    pub const fn is_signed_machine(self) -> bool {
        matches!(self, Self::I(_) | Self::ISize)
    }

    /// Width in bits of a machine type, or `None` for `Int` and `Nat`.
    #[must_use]
    pub const fn bits(self, pointer_width: u32) -> Option<u32> {
        match self {
            Self::Int | Self::Nat => None,
            Self::U(bits) | Self::I(bits) => Some(bits),
            Self::USize | Self::ISize => Some(pointer_width),
            Self::Char => Some(32),
        }
    }

    /// Is this a well-formed type? Fixed widths must be one of
    /// [`MACHINE_WIDTHS`].
    #[must_use]
    pub fn is_valid(self) -> bool {
        match self {
            Self::U(bits) | Self::I(bits) => MACHINE_WIDTHS.contains(&bits),
            _ => true,
        }
    }

    /// Smallest value, or `None` when unbounded below (`Int`). Call only on a
    /// type that [`Self::is_valid`] accepts; an invalid width gives a
    /// meaningless (but non-panicking) answer.
    #[must_use]
    pub fn min(self, pointer_width: u32) -> Option<i128> {
        match self {
            Self::Int => None,
            Self::Nat | Self::U(_) | Self::USize | Self::Char => Some(0),
            Self::I(_) | Self::ISize => {
                let bits = self.bits(pointer_width)?;
                // -2^(bits-1), by an arithmetic shift of -2^127.
                Some(
                    i128::MIN
                        .checked_shr(128u32.checked_sub(bits)?)
                        .unwrap_or(0),
                )
            }
        }
    }

    /// Largest value, or `None` when unbounded above (`Int`, `Nat`). Same
    /// precondition as [`Self::min`].
    #[must_use]
    pub fn max(self, pointer_width: u32) -> Option<u128> {
        match self {
            Self::Int | Self::Nat => None,
            Self::Char => Some(0x10_FFFF),
            Self::U(_) | Self::USize => {
                let bits = self.bits(pointer_width)?;
                // 2^bits - 1.
                Some(
                    u128::MAX
                        .checked_shr(128u32.checked_sub(bits)?)
                        .unwrap_or(0),
                )
            }
            Self::I(_) | Self::ISize => {
                let bits = self.bits(pointer_width)?;
                // 2^(bits-1) - 1.
                Some(
                    u128::MAX
                        .checked_shr(129u32.checked_sub(bits)?)
                        .unwrap_or(0),
                )
            }
        }
    }

    /// Does every value of `other` belong to `self`?
    #[must_use]
    pub fn contains(self, other: Self, pointer_width: u32) -> bool {
        let lower_ok = match (self.min(pointer_width), other.min(pointer_width)) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(mine), Some(theirs)) => mine <= theirs,
        };
        let upper_ok = match (self.max(pointer_width), other.max(pointer_width)) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(mine), Some(theirs)) => mine >= theirs,
        };
        lower_ok && upper_ok
    }
}

/// A VcIR type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    /// `bool`.
    Bool,
    /// An integer type.
    Int(IntRange),
    /// `()`.
    Unit,
    /// A tuple of one or more elements. The empty tuple is [`Self::Unit`].
    Tuple(Vec<Ty>),
    /// A struct or enum, with one type argument per type parameter of its
    /// declaration ([`crate::AdtDecl::type_params`]).
    Adt(AdtId, Vec<Ty>),
    /// A reference. Shared references are transparent to verification; a
    /// mutable reference parameter has a value at entry (`Old`) and a current
    /// value.
    Ref {
        /// `&mut` rather than `&`.
        mutable: bool,
        /// The referenced type.
        inner: Box<Ty>,
    },
    /// Type parameter `n` of the enclosing function
    /// ([`crate::FnDecl::type_params`]). Its values are opaque: they are
    /// compared with `==`, passed to functions and returned, and nothing
    /// else is known about them.
    Param(u32),
}

impl Ty {
    /// The `int` type.
    #[must_use]
    pub const fn int() -> Self {
        Self::Int(IntRange::Int)
    }

    /// The `nat` type.
    #[must_use]
    pub const fn nat() -> Self {
        Self::Int(IntRange::Nat)
    }

    /// An unsigned machine type.
    #[must_use]
    pub const fn uint(bits: u32) -> Self {
        Self::Int(IntRange::U(bits))
    }

    /// A signed machine type.
    #[must_use]
    pub const fn sint(bits: u32) -> Self {
        Self::Int(IntRange::I(bits))
    }

    /// The integer range, when this is an integer type.
    #[must_use]
    pub const fn int_range(&self) -> Option<IntRange> {
        match self {
            Self::Int(range) => Some(*range),
            _ => None,
        }
    }

    /// Strip one reference, if any.
    #[must_use]
    pub fn deref(&self) -> Option<&Self> {
        match self {
            Self::Ref { inner, .. } => Some(inner),
            _ => None,
        }
    }

    /// `self` with every type parameter `Param(n)` replaced by `args[n]`;
    /// a parameter without an argument stays.
    #[must_use]
    pub fn subst(&self, args: &[Self]) -> Self {
        match self {
            Self::Param(n) => args.get(*n as usize).cloned().unwrap_or(Self::Param(*n)),
            Self::Tuple(elems) => Self::Tuple(elems.iter().map(|e| e.subst(args)).collect()),
            Self::Ref { mutable, inner } => Self::Ref {
                mutable: *mutable,
                inner: Box::new(inner.subst(args)),
            },
            Self::Adt(id, targs) => Self::Adt(*id, targs.iter().map(|t| t.subst(args)).collect()),
            Self::Bool | Self::Int(_) | Self::Unit => self.clone(),
        }
    }

    /// Does the type mention a type parameter?
    #[must_use]
    pub fn has_param(&self) -> bool {
        match self {
            Self::Param(_) => true,
            Self::Tuple(elems) => elems.iter().any(Self::has_param),
            Self::Ref { inner, .. } => inner.has_param(),
            Self::Adt(_, args) => args.iter().any(Self::has_param),
            Self::Bool | Self::Int(_) | Self::Unit => false,
        }
    }
}
